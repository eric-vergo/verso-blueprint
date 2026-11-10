"""Browser checks for the Blueprint sidebar (`--sidebar`) and its theme switch."""

import subprocess
import sys
from pathlib import Path

import pytest
from playwright.sync_api import Page, expect

from scripts.blueprint_harness_paths import canonical_test_blueprint_output_dir
from scripts.blueprint_harness_utils import lean_low_priority_command
from support import PACKAGE_ROOT, assert_no_runtime_errors, find_free_port, record_runtime_errors, wait_for_server


@pytest.fixture(scope="session")
def sidebar_site_dir() -> Path:
    output_dir = canonical_test_blueprint_output_dir("preview_runtime_showcase", Path(__file__))
    output_dir = output_dir.parent / (output_dir.name + "-sidebar")
    output_dir.parent.mkdir(parents=True, exist_ok=True)
    project_dir = PACKAGE_ROOT / "tests" / "test_blueprints" / "preview_runtime_showcase"
    subprocess.run(
        lean_low_priority_command(PACKAGE_ROOT, "lake", "build", "PreviewRuntimeShowcase"),
        cwd=project_dir,
        check=True,
    )
    subprocess.run(
        lean_low_priority_command(
            PACKAGE_ROOT,
            "lake",
            "lean",
            "PreviewRuntimeShowcaseMain.lean",
            "--",
            "--run",
            "PreviewRuntimeShowcaseMain.lean",
            "--output",
            str(output_dir),
            "--without-html-single",
            "--sidebar",
        ),
        cwd=project_dir,
        check=True,
    )
    return output_dir / "html-multi"


@pytest.fixture(scope="session")
def sidebar_server(sidebar_site_dir: Path):
    port = find_free_port()
    proc = subprocess.Popen(
        [sys.executable, "-m", "http.server", str(port), "--bind", "127.0.0.1"],
        cwd=sidebar_site_dir,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    url = f"http://127.0.0.1:{port}"
    wait_for_server(url, proc)
    yield url
    proc.terminate()
    proc.wait()


class TestSidebarRuntime:
    def test_sidebar_entries(self, sidebar_server: str, page: Page):
        errors = record_runtime_errors(page)
        page.goto(sidebar_server + "/")
        toc = page.locator("#toc")
        expect(toc.locator("tr.bp_sidebar_home a")).to_have_text("Blueprint Home")
        expect(toc.locator("tr.bp_sidebar_rule").first).to_be_attached()
        expect(toc.locator(".bp_sidebar_foot .bp_theme_switch")).to_be_visible()
        assert_no_runtime_errors(errors)

    def test_theme_switch_persists_across_reload(self, sidebar_server: str, page: Page):
        page.emulate_media(color_scheme="light")
        page.goto(sidebar_server + "/")
        switch = page.locator(".bp_theme_switch")
        expect(switch).to_have_attribute("aria-checked", "false")
        switch.click()
        expect(page.locator("html")).to_have_attribute("data-theme", "dark")
        expect(switch).to_have_attribute("aria-checked", "true")
        assert page.evaluate("localStorage.getItem('verso-theme')") == "dark"
        page.reload()
        # applied by the inline <head> script, before the sidebar script runs
        expect(page.locator("html")).to_have_attribute("data-theme", "dark")
        expect(page.locator(".bp_theme_switch")).to_have_attribute("aria-checked", "true")
        page.locator(".bp_theme_switch").click()
        expect(page.locator("html")).to_have_attribute("data-theme", "light")
        assert page.evaluate("localStorage.getItem('verso-theme')") == "light"

    def test_switch_follows_os_preference_without_stored_choice(self, sidebar_server: str, page: Page):
        page.emulate_media(color_scheme="dark")
        page.goto(sidebar_server + "/")
        page.evaluate("localStorage.removeItem('verso-theme')")
        page.reload()
        expect(page.locator(".bp_theme_switch")).to_have_attribute("aria-checked", "true")
