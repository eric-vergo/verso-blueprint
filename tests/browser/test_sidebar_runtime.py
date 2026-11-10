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

    def test_sections_nest_under_their_chapter(self, sidebar_server: str, page: Page):
        errors = record_runtime_errors(page)
        page.goto(sidebar_server + "/External-Declaration-Heading-Repro/Nested-External-Declaration-Panels/")
        toc = page.locator("#toc")
        chapter = toc.locator(".split-toc.book > table > tbody > tr.numbered.current")
        expect(chapter).to_have_count(1)
        # the chapter's sections follow it directly, the current one marked
        nested = chapter.locator("xpath=following-sibling::tr[1]")
        expect(nested).to_have_class("bp_sidebar_sections")
        expect(nested.locator("tr.current a")).to_have_text("Nested External Declaration Panels")
        # Verso's separate per-level lists are gone: the section is listed once
        for split_toc in toc.locator(".split-toc:not(.book)").all():
            expect(split_toc).to_be_hidden()
        expect(toc.locator("a:visible", has_text="Nested External Declaration Panels")).to_have_count(1)
        # the current entry is bold, without Verso's dotted underline
        decoration = chapter.locator("td:not(.num)").evaluate("e => getComputedStyle(e).textDecorationLine")
        assert decoration == "none"
        assert_no_runtime_errors(errors)

    def test_header_sits_at_the_top_of_the_sidebar(self, sidebar_server: str, page: Page):
        page.set_viewport_size({"width": 1280, "height": 800})
        page.goto(sidebar_server + "/Code-Panels/")
        header = page.locator("body > header").bounding_box()
        toc = page.locator("#toc").bounding_box()
        assert header is not None and toc is not None
        assert header["x"] == 0 and abs(header["width"] - toc["width"]) < 1
        assert toc["y"] >= header["y"] + header["height"] - 1
        # the page content starts at the top of the window, beside the sidebar
        content = page.locator("main .content-wrapper").bounding_box()
        assert content is not None and content["y"] < 40
        expect(page.locator("body > header .header-title")).to_be_visible()

    def test_page_controls_move_into_the_sidebar_foot(self, sidebar_server: str, page: Page):
        page.goto(sidebar_server + "/Code-Panels/")
        switcher = page.locator("#bp-style-switcher")
        expect(switcher).to_have_count(1)
        expect(page.locator(".bp_sidebar_foot #bp-style-switcher")).to_be_visible()
        assert switcher.evaluate("e => getComputedStyle(e).position") == "static"

    @pytest.mark.parametrize("scheme", ["light", "dark"])
    def test_sidebar_text_contrast(self, sidebar_server: str, page: Page, scheme: str):
        page.emulate_media(color_scheme=scheme)
        page.goto(sidebar_server + "/Code-Panels/")
        ratios = page.evaluate(
            """() => {
              const parse = (c) => { const p = c.match(/[\\d.]+/g).map(Number); return { r: p[0], g: p[1], b: p[2], a: p.length > 3 ? p[3] : 1 }; };
              const lum = (c) => { const f = (v) => { v /= 255; return v <= 0.03928 ? v / 12.92 : Math.pow((v + 0.055) / 1.055, 2.4); }; return 0.2126 * f(c.r) + 0.7152 * f(c.g) + 0.0722 * f(c.b); };
              const bg = parse(getComputedStyle(document.getElementById('toc')).backgroundColor);
              const ratio = (el) => {
                const fg = parse(getComputedStyle(el).color);
                const seen = { r: fg.r * fg.a + bg.r * (1 - fg.a), g: fg.g * fg.a + bg.g * (1 - fg.a), b: fg.b * fg.a + bg.b * (1 - fg.a) };
                const [x, y] = [lum(seen), lum(bg)].sort((p, q) => q - p);
                return (x + 0.05) / (y + 0.05);
              };
              return [...document.querySelectorAll('#toc a, #toc td.num, .bp_sidebar_foot label, .bp_sidebar_foot summary')]
                .filter((el) => el.offsetParent !== null && el.textContent.trim())
                .map((el) => [el.textContent.trim().slice(0, 30), ratio(el)]);
            }"""
        )
        assert ratios
        failing = [r for r in ratios if r[1] < 4.5]
        assert not failing, failing

    @pytest.mark.parametrize("scheme", ["light", "dark"])
    def test_adopted_folded_control_keeps_contrast(self, sidebar_server: str, page: Page, scheme: str):
        # A page control adopted into the foot (like the status legend) whose own CSS gives its
        # summary the faint text colour of a light page must still read on the sidebar.
        page.emulate_media(color_scheme=scheme)
        page.goto(sidebar_server + "/Code-Panels/")
        ratio = page.evaluate(
            """() => {
              const style = document.createElement('style');
              style.textContent = '.bp_probe_control > summary { color: #94a3b8; }';
              document.head.appendChild(style);
              const host = document.querySelector('.bp_sidebar_foot_extra');
              const control = document.createElement('details');
              control.className = 'bp_probe_control';
              control.innerHTML = '<summary>Status legend</summary><p>x</p>';
              host.appendChild(control);
              const parse = (c) => { const p = c.match(/[\\d.]+/g).map(Number); return { r: p[0], g: p[1], b: p[2], a: p.length > 3 ? p[3] : 1 }; };
              const lum = (c) => { const f = (v) => { v /= 255; return v <= 0.03928 ? v / 12.92 : Math.pow((v + 0.055) / 1.055, 2.4); }; return 0.2126 * f(c.r) + 0.7152 * f(c.g) + 0.0722 * f(c.b); };
              const bg = parse(getComputedStyle(document.getElementById('toc')).backgroundColor);
              const fg = parse(getComputedStyle(control.querySelector('summary')).color);
              const seen = { r: fg.r * fg.a + bg.r * (1 - fg.a), g: fg.g * fg.a + bg.g * (1 - fg.a), b: fg.b * fg.a + bg.b * (1 - fg.a) };
              const [x, y] = [lum(seen), lum(bg)].sort((p, q) => q - p);
              return (x + 0.05) / (y + 0.05);
            }"""
        )
        assert ratio >= 4.5, ratio
