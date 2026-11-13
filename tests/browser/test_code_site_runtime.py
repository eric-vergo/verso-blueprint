"""Browser checks for a site generated from compiled-code data (`vbp code-site`).

The site is generated from `code_site_fixture/` (four modules, one with a long dotted name, a
declaration chain a <- b <- c <- d with source occurrences and hover texts). The checks: the
dependency graph's first view is drawn before the page scripts have run and is then laid out
from build-time positions, the ego view around a declaration with its hop count, the node view's
and the chapter entry's neighbourhood links, the highlighted source excerpt's hovers, the search
box finding a declaration, and long module names wrapping in the sidebar.
"""

import shutil
import subprocess
import sys
from pathlib import Path

import pytest
from playwright.sync_api import Page

from scripts.blueprint_harness_paths import canonical_test_blueprint_output_dir
from support import PACKAGE_ROOT, find_free_port, wait_for_server

FIXTURE = Path(__file__).parent / "code_site_fixture"


def vbp_executable() -> Path:
    exe = PACKAGE_ROOT / ".lake" / "build" / "bin" / "vbp"
    if not exe.exists():
        subprocess.run(["lake", "build", "vbp"], cwd=PACKAGE_ROOT, check=True)
    return exe


@pytest.fixture(scope="session")
def code_site_dir() -> Path:
    output_dir = canonical_test_blueprint_output_dir("code_site_fixture", Path(__file__))
    if output_dir.exists():
        shutil.rmtree(output_dir)
    output_dir.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(
        [str(vbp_executable()), "code-site", "--data", str(FIXTURE / "code-site.json"),
         "--root", str(FIXTURE), "--output", str(output_dir), "--reproducible"],
        cwd=FIXTURE,
        check=True,
    )
    return output_dir / "html-multi"


@pytest.fixture(scope="session")
def code_site_url(code_site_dir: Path):
    port = find_free_port()
    proc = subprocess.Popen(
        [sys.executable, "-m", "http.server", str(port), "--bind", "127.0.0.1"],
        cwd=code_site_dir,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    url = f"http://127.0.0.1:{port}"
    wait_for_server(url, proc)
    yield url
    proc.terminate()
    proc.wait()


def wait_for_interactive_graph(page: Page) -> None:
    page.wait_for_function(
        """() => {
            const node = document.querySelector(".bp_graph_canvas svg g.node");
            const block = document.querySelector(".bp_graph_fullwidth");
            const state = block ? block.__bpGraphState : null;
            return !!node && !!node.__data__ && !!state && state.renderFinalizedToken === state.renderToken;
        }""",
        timeout=60000,
    )


def drawn_labels(page: Page) -> list[str]:
    return page.evaluate(
        """() => Array.from(document.querySelectorAll(".bp_graph_canvas svg g.node text"))
            .map((t) => t.textContent.trim()).sort()"""
    )


def test_first_view_is_drawn_from_build_time_layout(page: Page, code_site_dir: Path, code_site_url: str):
    if shutil.which("dot") is None:
        pytest.skip("Graphviz `dot` is not installed: the generator leaves the layout to the page")
    html = (code_site_dir / "Dependency-Graph" / "index.html").read_text(encoding="utf-8")
    assert '<svg class="bp_graph_prerendered" data-variant="full"' in html
    assert 'class="bp-graph-layout" data-variant="full"' in html
    page.goto(code_site_url + "/Dependency-Graph/", wait_until="domcontentloaded")
    wait_for_interactive_graph(page)
    assert page.locator(".bp_graph_canvas").get_attribute("data-bp-graph-layout-source") == "build"
    assert page.locator(".bp_graph_prerender_overlay").count() == 0
    assert drawn_labels(page) == ["Demo.b", "Demo.c", "Demo.d", "a"]


def test_ego_view_and_hops(page: Page, code_site_url: str):
    page.goto(code_site_url + "/Dependency-Graph/#ego=Demo.b&k=1", wait_until="domcontentloaded")
    wait_for_interactive_graph(page)
    assert page.locator(".bp_graph_view_select").input_value() == "ego"
    assert drawn_labels(page) == ["Demo.b", "Demo.c", "a"]
    assert page.locator(".bp_graph_canvas svg g.node.bp_graph_ego_center").count() == 1
    hops = page.locator(".bp_graph_ego_hops")
    assert hops.is_visible()
    hops.select_option("2")
    page.wait_for_function("document.querySelectorAll('.bp_graph_canvas svg g.node').length === 4")
    wait_for_interactive_graph(page)
    assert page.evaluate("location.hash") == "#ego=Demo.b&k=2"
    page.locator(".bp_graph_view_select").select_option("full")
    page.wait_for_function("!document.querySelector('.bp_graph_ego_hops_label') || document.querySelector('.bp_graph_ego_hops_label').hidden")


def test_node_view_links_to_its_neighbourhood(page: Page, code_site_url: str):
    page.goto(code_site_url + "/Dependency-Graph/#node=Demo.c", wait_until="domcontentloaded")
    page.wait_for_selector(".bp_graph_preview .bp_node_view", timeout=60000)
    link = page.locator(".bp_graph_preview .bp_node_view_header a.bp_node_view_ego")
    assert link.get_attribute("href").endswith("/Dependency-Graph/#ego=Demo.c&k=1")
    link.click()
    page.wait_for_function("document.querySelector('.bp_graph_view_select').value === 'ego'")
    wait_for_interactive_graph(page)
    assert drawn_labels(page) == ["Demo.b", "Demo.c", "Demo.d", "a"]


def test_chapter_entry_highlighted_source_with_hovers(page: Page, code_site_url: str):
    page.goto(code_site_url + "/Demo___A/", wait_until="load")
    assert "The first module." in page.locator("main").inner_text()
    ego = page.locator("a.bp_external_decl_ego").first
    assert ego.get_attribute("href") == "Dependency-Graph/#ego=Demo.a"
    page.evaluate("""() => document.querySelectorAll("details").forEach((d) => { d.open = true; })""")
    source = page.locator(".bp_plain_decl_source pre").first
    assert source.locator(".keyword.token").first.inner_text() == "def"
    nat = source.locator(".const.token[data-verso-hover]").filter(has_text="Nat").first
    nat.scroll_into_view_if_needed()
    nat.hover()
    page.wait_for_selector(".tippy-box", timeout=10000)
    assert "Nat : Type" in page.locator(".tippy-box").first.inner_text()


def test_search_finds_a_declaration(page: Page, code_site_url: str):
    page.goto(code_site_url + "/", wait_until="load")
    page.locator("#cb1-input").click()
    page.keyboard.type("Demo.c")
    page.wait_for_selector("[role=option]", timeout=10000)
    options = page.locator("[role=option]").all_inner_texts()
    assert any("Demo.c" in o and "Documentation" in o for o in options)


def test_long_module_names_wrap_in_the_sidebar(page: Page, code_site_url: str):
    page.set_viewport_size({"width": 1280, "height": 800})
    page.goto(code_site_url + "/", wait_until="load")
    entry = page.locator("#toc a", has_text="ForTheSidebar").first
    assert entry.locator("wbr").count() > 0
    assert page.evaluate(
        """() => {
            const a = Array.from(document.querySelectorAll("#toc a")).find((x) => x.textContent.includes("ForTheSidebar"));
            const cell = a.closest("td");
            return cell.scrollWidth <= cell.clientWidth + 1;
        }"""
    )
