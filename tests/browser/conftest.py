import pytest
from contextlib import ExitStack, contextmanager
import atexit
import os
import random
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from playwright.sync_api import sync_playwright

from support import (PACKAGE_ROOT, find_free_port, record_builds, wait_for_server,
                     write_large_code_site)

if str(PACKAGE_ROOT) not in sys.path:
    sys.path.insert(0, str(PACKAGE_ROOT))

from scripts.blueprint_harness_paths import (
    canonical_test_blueprint_output_dir,
)


# A kernel replay that accepts records that it did in a file; every site these tests generate,
# here and in the processes they start, records into a scratch folder, never the user's cache.
REPLAY_RECORD_DIR = Path(tempfile.mkdtemp(prefix="vbp-browser-replay-record-"))
atexit.register(shutil.rmtree, REPLAY_RECORD_DIR, ignore_errors=True)
os.environ["VERSO_BLUEPRINT_KERNEL_REPLAY_RECORD"] = str(REPLAY_RECORD_DIR / "kernel-replay-checkers.json")

DEFAULT_TEST_BLUEPRINT = "preview_runtime_showcase"
DEFAULT_BROWSER_TYPES = {"chromium"}


def selected_browser_types(selected) -> set[str]:
    if isinstance(selected, (list, tuple, set)):
        return set(selected) or set(DEFAULT_BROWSER_TYPES)
    if selected in (None, ""):
        return set(DEFAULT_BROWSER_TYPES)
    return {selected}


def browser_executable(browser_type: str) -> str | None:
    candidates = {
        "chromium": ["google-chrome", "chromium", "chromium-browser"],
        "firefox": ["firefox"],
    }.get(browser_type, [])
    for candidate in candidates:
        path = shutil.which(candidate)
        if path:
            return path
    return None


def build_test_blueprint_site(name: str) -> Path:
    output_dir = canonical_test_blueprint_output_dir(name, Path(__file__))
    output_dir.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(
        [
            sys.executable,
            "-m",
            "scripts.blueprint_test_blueprints",
            "generate-all",
            name,
        ],
        cwd=PACKAGE_ROOT,
        check=True,
    )
    return output_dir / "html-multi"


def pytest_addoption(parser):
    parser.addoption(
        "--test-blueprint",
        action="store",
        default=DEFAULT_TEST_BLUEPRINT,
        help="Named in-repo test blueprint to build and serve by default",
    )
    parser.addoption(
        "--port",
        action="store",
        default=None,
        help="Port for the local test server (default: auto-select)",
    )
    parser.addoption(
        "--site-dir",
        action="store",
        default=None,
        help="Path to the built site directory (overrides --test-blueprint)",
    )
    parser.addoption(
        "--server-url",
        action="store",
        default=None,
        help="Use an existing server instead of starting one (e.g., http://localhost:3000)",
    )
    parser.addoption(
        "--seed",
        action="store",
        default=None,
        type=int,
        help="Random seed for reproducible redirect selection",
    )


def pytest_configure(config):
    seed = config.getoption("--seed")
    if seed is not None:
        random.seed(seed)


@pytest.fixture(scope="session")
def server(request):
    external_url = request.config.getoption("--server-url")

    if external_url:
        yield external_url
        return

    site_dir = request.config.getoption("--site-dir")
    if site_dir is None:
        site_dir = build_test_blueprint_site(request.config.getoption("--test-blueprint"))
    else:
        site_dir = Path(site_dir)
        if not site_dir.is_absolute():
            site_dir = (Path(__file__).parent / site_dir).resolve()
    port = request.config.getoption("--port")
    with serve_site(site_dir, int(port) if port is not None else None) as url:
        yield url


@contextmanager
def serve_site(site_dir: Path, port: int | None = None):
    port = find_free_port() if port is None else port
    proc = subprocess.Popen(
        [sys.executable, "-m", "http.server", str(port), "--bind", "127.0.0.1"],
        cwd=site_dir,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    url = f"http://127.0.0.1:{port}"
    try:
        wait_for_server(url, proc)
        yield url
    finally:
        proc.terminate()
        proc.wait()


@pytest.fixture(scope="session")
def named_site():
    """Build and serve each requested fixture once, sharing lifecycle cleanup."""
    with ExitStack() as stack:
        sites = {}

        def get_site(name: str) -> str:
            if name not in sites:
                sites[name] = stack.enter_context(serve_site(build_test_blueprint_site(name)))
            return sites[name]

        yield get_site


@pytest.fixture(scope="session")
def playwright_instance():
    with sync_playwright() as p:
        yield p


@pytest.fixture(scope="session", params=["chromium", "firefox"])
def browser(request, playwright_instance):
    browser_type = request.param
    selected_browsers = selected_browser_types(request.config.getoption("browser"))
    if browser_type not in selected_browsers:
        pytest.skip(f"browser {browser_type} not selected")
    launcher = getattr(playwright_instance, browser_type)
    try:
        browser = launcher.launch()
    except Exception as err:
        executable = browser_executable(browser_type)
        if executable is None:
            pytest.skip(f"no Playwright-managed or system browser available for {browser_type}: {err}")
        browser = launcher.launch(executable_path=executable)
    yield browser
    browser.close()


@pytest.fixture
def page(browser):
    page = browser.new_page()
    yield page
    page.close()


CODE_SITE_FIXTURE = Path(__file__).parent / "code_site_fixture"


def vbp_executable() -> Path:
    exe = PACKAGE_ROOT / ".lake" / "build" / "bin" / "vbp"
    if not exe.exists():
        subprocess.run(["lake", "build", "vbp"], cwd=PACKAGE_ROOT, check=True)
    return exe


def generate_code_site(data: Path, root: Path, output_dir: Path, *flags: str) -> Path:
    """Runs `vbp code-site` and returns the site's `html-multi` folder."""
    if output_dir.exists():
        shutil.rmtree(output_dir)
    output_dir.parent.mkdir(parents=True, exist_ok=True)
    # Verso looks for the project of a site by its `lean-toolchain`; a project written to a
    # temporary folder has none of its own
    if not any((folder / "lean-toolchain").exists() for folder in (root, *root.parents)):
        shutil.copy(PACKAGE_ROOT / "lean-toolchain", root / "lean-toolchain")
    subprocess.run(
        [str(vbp_executable()), "code-site", "--data", str(data), "--root", str(root),
         "--output", str(output_dir), "--reproducible", *flags],
        cwd=root,
        check=True,
    )
    return output_dir / "html-multi"


@pytest.fixture(scope="session")
def code_site_dir(tmp_path_factory) -> Path:
    """The site of a copy of `code_site_fixture/`, four declarations in a chain, each module with
    a build record of its source as it is (`record_builds`)."""
    root = tmp_path_factory.mktemp("code-site-fixture") / "project"
    shutil.copytree(CODE_SITE_FIXTURE, root)
    record_builds(root, root / "code-site.json")
    return generate_code_site(root / "code-site.json", root, root.parent / "_out")


@pytest.fixture(scope="session")
def code_site_url(code_site_dir: Path):
    with serve_site(code_site_dir) as url:
        yield url


@pytest.fixture(scope="session")
def large_site_dir(tmp_path_factory) -> Path:
    """A generated site of a graph of 384 declarations in two connected components and eight
    groups (one per module), so it opens on the group view."""
    root = tmp_path_factory.mktemp("large-code-site")
    data = write_large_code_site(root)
    return generate_code_site(
        data, root, root / "_out", "--no-kernel-replay", "--no-comparator", "--no-stats-page"
    )


@pytest.fixture(scope="session")
def large_site_url(large_site_dir: Path):
    with serve_site(large_site_dir) as url:
        yield url


@pytest.fixture(scope="session")
def mid_site_url(tmp_path_factory):
    """A generated site of 64 declarations in four chains of modules, whose full graph drawn top
    down is a little too wide for a 1400 px window at the readable scale."""
    root = tmp_path_factory.mktemp("mid-code-site")
    data = write_large_code_site(root, modules=4, per_module=16, chains=4)
    site = generate_code_site(
        data, root, root / "_out", "--no-kernel-replay", "--no-comparator", "--no-stats-page"
    )
    with serve_site(site) as url:
        yield url
