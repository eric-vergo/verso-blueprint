from __future__ import annotations

import functools
import http.server
import json
import socket
import subprocess
import threading
import time
import urllib.request
from contextlib import contextmanager
from pathlib import Path

from playwright.sync_api import Page


PACKAGE_ROOT = Path(__file__).resolve().parents[2]


def find_free_port() -> int:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


def wait_for_server(url: str, proc: subprocess.Popen[bytes], timeout_s: float = 10.0) -> None:
    deadline = time.time() + timeout_s
    while time.time() < deadline:
        if proc.poll() is not None:
            raise RuntimeError(f"local test server exited early with code {proc.returncode}")
        try:
            with urllib.request.urlopen(url):
                return
        except OSError:
            time.sleep(0.1)
    raise RuntimeError(f"timed out waiting for local test server at {url}")


def record_runtime_errors(page: Page) -> list[str]:
    errors: list[str] = []

    page.on("pageerror", lambda exc: errors.append(str(exc)))

    def on_console(msg) -> None:
        if msg.type == "error":
            errors.append(msg.text)

    page.on("console", on_console)
    return errors


def assert_no_runtime_errors(errors: list[str]) -> None:
    relevant = [
        err
        for err in errors
        if "cancelChildHide" in err or "ReferenceError" in err or "Uncaught" in err
    ]
    assert not relevant, "\n".join(relevant)


def blueprint_render_api_script(body: str) -> str:
    return f"""
    async () => {{
        async function loadBlueprintRenderApi() {{
            const moduleUrl = new URL(
                "-verso-data/blueprint-page-runtime.mjs",
                document.baseURI
            ).href;
            const runtime = await import(moduleUrl);
            if (runtime && runtime.blueprintPageRuntime) {{
                return runtime.blueprintPageRuntime;
            }}
            throw new Error("Blueprint page runtime did not expose a render API");
        }}
        const api = await loadBlueprintRenderApi();
        {body}
    }}
    """


def wait_for_blueprint_render_api(page: Page) -> None:
    page.evaluate(blueprint_render_api_script("return true;"))


def wait_for_graph_rendered(page: Page, timeout: float = 60000) -> None:
    """The graph's interactive drawing is on screen: a drawing under pan and zoom is the canvas's
    own child (the first drawing the page was written with is inside `.bp_graph_first_drawing`),
    and the render that made it is the latest one."""
    page.wait_for_function(
        """() => {
            const canvas = document.querySelector(".bp_graph_canvas");
            const svg = canvas ? canvas.querySelector(":scope > svg") : null;
            const block = document.querySelector(".bp_graph_fullwidth");
            const state = block ? block.__bpGraphState : null;
            return !!svg && !!svg.querySelector("g.node") && !!state &&
                state.renderFinalizedToken === state.renderToken;
        }""",
        timeout=timeout,
    )


def graph_scale(page: Page) -> float:
    """The scale the drawing is shown at (`data-bp-graph-scale` of its `svg`)."""
    return page.evaluate(
        """() => parseFloat(
            document.querySelector(".bp_graph_canvas > svg").getAttribute("data-bp-graph-scale"))"""
    )


def graph_transform(page: Page) -> str | None:
    """The transform of the drawing's `g.graph`: pan and zoom."""
    return page.evaluate(
        """() => {
            const svg = document.querySelector(".bp_graph_canvas > svg");
            const graph = svg ? svg.querySelector("g.graph") : null;
            return graph ? graph.getAttribute("transform") : null;
        }"""
    )


def node_centre(page: Page, label: str) -> dict:
    """The centre of the node named `label` on screen."""
    return page.evaluate(
        """(label) => {
            const node = Array.from(document.querySelectorAll(".bp_graph_canvas > svg g.node"))
                .find((n) => n.getAttribute("data-bp-node-name") === label);
            if (!node) return null;
            const r = node.getBoundingClientRect();
            return { x: r.left + r.width / 2, y: r.top + r.height / 2,
                     width: r.width, height: r.height };
        }""",
        label,
    )


@contextmanager
def serve_with_headers(site_dir: Path, headers: dict[str, str]):
    """Serves `site_dir` with extra response headers; yields the base URL. The server runs on a
    thread of this process and stops on exit."""

    class Handler(http.server.SimpleHTTPRequestHandler):
        def end_headers(self) -> None:
            for name, value in headers.items():
                self.send_header(name, value)
            super().end_headers()

        def log_message(self, *_args) -> None:
            pass

    handler = functools.partial(Handler, directory=str(site_dir))
    httpd = http.server.ThreadingHTTPServer(("127.0.0.1", 0), handler)
    thread = threading.Thread(target=httpd.serve_forever, daemon=True)
    thread.start()
    try:
        yield f"http://127.0.0.1:{httpd.server_address[1]}"
    finally:
        httpd.shutdown()
        httpd.server_close()
        thread.join()


def large_code_site_data(modules: int = 8, per_module: int = 48, chains: int = 2) -> dict:
    """Data for `vbp code-site` of a large dependency graph: `modules` modules of `per_module`
    declarations each, in `chains` separate families of modules (so the graph has that many
    connected components). In a module every declaration uses its parent in a binary tree; the
    first declaration of a module uses the last of the previous module of its family. Every node
    has one path to each of its ancestors, which keeps the build's own work on the graph linear."""
    out = []
    for m in range(modules):
        family = m % chains
        declarations = []
        for i in range(per_module):
            name = f"Big.f{family}.m{m}.d{i}"
            uses = []
            if i >= 1:
                uses.append({"name": f"Big.f{family}.m{m}.d{(i - 1) // 2}", "kind": "statement"})
            elif m >= chains:
                uses.append({"name": f"Big.f{family}.m{m - chains}.d{per_module - 1}",
                             "kind": "statement"})
            declarations.append({
                "name": name, "kind": "theorem" if i % 3 else "def",
                "signature": f"theorem {name} : True",
                "range": {"start": {"line": i, "character": 0}, "end": {"line": i, "character": 10}},
                "uses": uses,
            })
        out.append({"module": f"Big.M{m}", "source": f"Big/M{m}.lean", "declarations": declarations})
    return {"format": "verso-blueprint-code-1", "title": "Large code site", "modules": out}


def write_large_code_site(root: Path, **kwargs) -> Path:
    """Writes the data of `large_code_site_data` under `root`; returns the data file."""
    root.mkdir(parents=True, exist_ok=True)
    data = root / "code-site.json"
    data.write_text(json.dumps(large_code_site_data(**kwargs)), encoding="utf-8")
    return data
