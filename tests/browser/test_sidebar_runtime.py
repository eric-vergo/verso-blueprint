"""Browser checks for the Blueprint sidebar (`--sidebar`) and the theme control in it."""

import functools
import http.server
import json
import re
import subprocess
import sys
import threading
import time
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


@pytest.fixture(scope="session")
def sidebar_single_site_dir() -> Path:
    """The showcase as one page (`html-single`) with the sidebar."""
    output_dir = canonical_test_blueprint_output_dir("preview_runtime_showcase", Path(__file__))
    output_dir = output_dir.parent / (output_dir.name + "-sidebar-single")
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
            "--with-html-single",
            "--without-html-multi",
            "--sidebar",
        ),
        cwd=project_dir,
        check=True,
    )
    return output_dir / "html-single"


def serve(directory: Path, delay_outline: float = 0.0):
    """Serve `directory` on 127.0.0.1, answering for the sidebar's outline after `delay_outline`
    seconds. Gives the server and its address."""

    class Handler(http.server.SimpleHTTPRequestHandler):
        def log_message(self, *args):
            pass

        def do_GET(self):
            if self.path.endswith("blueprint-sidebar-outline.js"):
                time.sleep(delay_outline)
            return super().do_GET()

    server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), functools.partial(Handler, directory=str(directory)))
    threading.Thread(target=server.serve_forever, daemon=True).start()
    return server, f"http://127.0.0.1:{server.server_address[1]}"


@pytest.fixture(scope="session")
def slow_outline_server(sidebar_site_dir: Path):
    server, url = serve(sidebar_site_dir, delay_outline=1.5)
    yield url
    server.shutdown()


@pytest.fixture(scope="session")
def sidebar_single_server(sidebar_single_site_dir: Path):
    server, url = serve(sidebar_single_site_dir)
    yield url
    server.shutdown()


class TestSidebarRuntime:
    def test_sidebar_entries(self, sidebar_server: str, page: Page):
        errors = record_runtime_errors(page)
        page.goto(sidebar_server + "/")
        toc = page.locator("#toc")
        expect(toc.locator("tr.bp_sidebar_home a")).to_have_text("Blueprint Home")
        expect(toc.locator("tr.bp_sidebar_rule").first).to_be_attached()
        # Verso's own theme control is in the table of contents, so the sidebar adds no second one
        expect(toc.locator("[data-verso-theme-toggle]")).to_be_visible()
        expect(toc.locator(".bp_theme_switch")).to_have_count(0)
        assert_no_runtime_errors(errors)

    def test_theme_choice_persists_across_reload(self, sidebar_server: str, page: Page):
        page.emulate_media(color_scheme="light")
        page.goto(sidebar_server + "/")
        dark = page.locator('[data-verso-theme-toggle] [data-theme-choice="dark"]')
        light = page.locator('[data-verso-theme-toggle] [data-theme-choice="light"]')
        expect(dark).to_have_attribute("aria-checked", "false")
        dark.click()
        expect(page.locator("html")).to_have_attribute("data-theme", "dark")
        expect(dark).to_have_attribute("aria-checked", "true")
        assert page.evaluate("localStorage.getItem('verso-theme')") == "dark"
        page.reload()
        # applied by the inline <head> script, before the page's other scripts run
        expect(page.locator("html")).to_have_attribute("data-theme", "dark")
        expect(dark).to_have_attribute("aria-checked", "true")
        light.click()
        expect(page.locator("html")).to_have_attribute("data-theme", "light")
        assert page.evaluate("localStorage.getItem('verso-theme')") == "light"

    def test_control_follows_os_preference_without_stored_choice(self, sidebar_server: str, page: Page):
        page.emulate_media(color_scheme="dark")
        page.goto(sidebar_server + "/")
        page.evaluate("localStorage.removeItem('verso-theme')")
        page.reload()
        auto = page.locator('[data-verso-theme-toggle] [data-theme-choice="auto"]')
        expect(auto).to_have_attribute("aria-checked", "true")
        assert page.evaluate("document.documentElement.getAttribute('data-theme')") is None
        assert page.evaluate("matchMedia('(prefers-color-scheme: dark)').matches")

    def test_sections_nest_under_their_chapter_without_the_outline(self, sidebar_server: str, page: Page):
        # Without the outline file the current chapter's sections are nested as Verso lists them.
        errors = record_runtime_errors(page)
        page.route("**/blueprint-sidebar-outline.js", lambda route: route.abort())
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
        expect(toc.locator(".bp_tree")).to_have_count(0)
        # the list is shown: the page does not wait for an outline that does not come
        expect(toc.locator(".split-toc.book")).to_be_visible()
        # the failed request for the outline is the only error
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
              return [...document.querySelectorAll('#toc a, #toc td.num, #toc .bp_tree_number, #toc .bp_part_number, .bp_sidebar_foot label, .bp_sidebar_foot summary')]
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


def tree_item(toc, title: str, exact: bool = True):
    """The tree item whose own row's title is `title` (or contains it, unless `exact`)."""
    text = re.compile(r"^\s*" + re.escape(title) + r"\s*$") if exact else title
    return toc.locator(".bp_tree_item").filter(
        has=toc.page.locator(":scope > .bp_tree_row .bp_tree_title", has_text=text)
    ).last


def own_row(item):
    return item.locator(":scope > .bp_tree_row")


def own_toggle(item):
    return item.locator(":scope > .bp_tree_row > .bp_tree_toggle")


SECTION_PAGE = "/Reading-Aids/A-Numbered-Section/"


class TestSidebarTree:
    def test_tree_levels_parts_and_current_page(self, sidebar_server: str, page: Page):
        errors = record_runtime_errors(page)
        page.set_viewport_size({"width": 1280, "height": 900})
        page.goto(sidebar_server + SECTION_PAGE)
        toc = page.locator("#toc")
        expect(toc.locator("ul.bp_tree")).to_have_count(1)
        # the parts, in order, at the top level, each with its chapters inside it
        parts = toc.locator("ul.bp_tree > li.bp_tree_part")
        expect(parts).to_have_count(2)
        expect(parts.nth(0).locator(":scope > .bp_tree_row .bp_part_number")).to_have_text("Part I")
        expect(parts.nth(1).locator(":scope > .bp_tree_row .bp_part_number")).to_have_text("Part II")
        part_two = parts.nth(1)
        chapter = tree_item(toc, "Reading Aids")
        section = tree_item(toc, "A Numbered Section")
        expect(part_two.locator(":scope > ul > li").filter(has_text="Reading Aids")).to_have_count(1)
        # the current page is marked, and everything above it is open
        expect(own_row(section)).to_have_class(re.compile(r"\bbp_tree_current\b"))
        expect(section.locator(":scope > .bp_tree_row > a")).to_have_attribute("aria-current", "page")
        expect(own_toggle(part_two)).to_have_attribute("aria-expanded", "true")
        expect(own_toggle(chapter)).to_have_attribute("aria-expanded", "true")
        expect(own_row(section)).to_be_visible()
        # the part's label is set apart: on its own line, in capitals, above a heavier title
        label = part_two.locator(":scope > .bp_tree_row .bp_part_label")
        assert label.evaluate("e => getComputedStyle(e).display") == "block"
        assert label.evaluate("e => getComputedStyle(e).textTransform") == "uppercase"
        part_weight = part_two.locator(":scope > .bp_tree_row > a").evaluate("e => getComputedStyle(e).fontWeight")
        chapter_weight = tree_item(toc, "Inline Hover Previews").locator(":scope > .bp_tree_row > a").evaluate(
            "e => getComputedStyle(e).fontWeight"
        )
        assert int(part_weight) > int(chapter_weight)
        # one indent per level, the same step each time
        def title_x(item):
            box = item.locator(":scope > .bp_tree_row .bp_tree_title").bounding_box()
            assert box is not None
            return box["x"]

        def toggle_x(item):
            box = item.locator(":scope > .bp_tree_row > :first-child").bounding_box()
            assert box is not None
            return box["x"]

        steps = [toggle_x(chapter) - toggle_x(part_two), toggle_x(section) - toggle_x(chapter)]
        assert steps[0] > 8 and abs(steps[0] - steps[1]) < 1, steps
        # a leaf row keeps the triangle's gutter, so its title lines up with its siblings'
        leaf, branch = tree_item(toc, "Side-by-Side Runs"), tree_item(toc, "Reading Aids")
        expect(own_toggle(branch)).to_have_count(1)
        assert abs(toggle_x(leaf) - toggle_x(branch)) < 0.5
        widths = [
            item.locator(":scope > .bp_tree_row > :first-child").evaluate("e => e.getBoundingClientRect().width")
            for item in (leaf, branch)
        ]
        assert abs(widths[0] - widths[1]) < 0.5, widths
        # a guide line per open level, running down its rows, under its entry's triangle
        group = chapter.locator(":scope > ul.bp_tree_group")
        guide = group.evaluate(
            """e => { const s = getComputedStyle(e, '::before');
                      return { width: s.borderLeftWidth, style: s.borderLeftStyle,
                               height: parseFloat(s.height), left: parseFloat(s.left),
                               group: e.getBoundingClientRect().height }; }"""
        )
        assert guide["width"] == "1px" and guide["style"] == "solid", guide
        assert guide["height"] >= guide["group"] - 4, guide
        triangle = own_toggle(chapter).bounding_box()
        group_box = group.bounding_box()
        assert triangle is not None and group_box is not None
        centre = triangle["x"] + triangle["width"] / 2 - group_box["x"]
        assert abs(guide["left"] - centre) <= 1.5, (guide, centre)
        # each triangle sits on the middle of its title's first line
        for item in (part_two, chapter, tree_item(toc, "External Declaration Heading Repro")):
            offset = item.evaluate(
                """e => { const row = e.querySelector(':scope > .bp_tree_row');
                          const t = row.querySelector('.bp_tree_toggle').getBoundingClientRect();
                          const before = getComputedStyle(row.querySelector('.bp_tree_toggle'), '::before');
                          const top = t.top + parseFloat(before.top);
                          // the triangle is drawn by its borders
                          const mid = top + (parseFloat(before.borderTopWidth) + parseFloat(before.borderBottomWidth)) / 2;
                          const title = row.querySelector('.bp_tree_title');
                          const box = title.getBoundingClientRect();
                          const lh = parseFloat(getComputedStyle(row.querySelector('a')).lineHeight);
                          // a part's title line is under its label; other rows' first line is on top
                          const centre = title.querySelector('.bp_part_label') ? box.bottom - lh / 2 : box.top + lh / 2;
                          return mid - centre; }"""
            )
            assert abs(offset) <= 2.5, offset
        # the triangle points down when open, right when closed
        closed = tree_item(toc, "Inline Hover Previews")
        assert own_toggle(chapter).evaluate("e => getComputedStyle(e, '::before').transform") != "none"
        assert own_toggle(closed).evaluate("e => getComputedStyle(e, '::before').transform") == "none"
        assert_no_runtime_errors(errors)

    def test_default_state_parts_open_chapters_closed(self, sidebar_server: str, page: Page):
        page.goto(sidebar_server + "/Code-Panels/")
        page.evaluate("sessionStorage.clear()")
        page.goto(sidebar_server + "/Code-Panels/")
        toc = page.locator("#toc")
        for part in toc.locator("ul.bp_tree > li.bp_tree_part").all():
            expect(own_toggle(part)).to_have_attribute("aria-expanded", "true")
        # every chapter is visible, chapters other than the current one are closed
        expect(own_row(tree_item(toc, "Reading Aids"))).to_be_visible()
        expect(own_toggle(tree_item(toc, "Reading Aids"))).to_have_attribute("aria-expanded", "false")
        expect(tree_item(toc, "A Numbered Section")).to_be_hidden()
        current = tree_item(toc, "Code Panels")
        expect(own_row(current)).to_have_class(re.compile(r"\bbp_tree_current\b"))
        if own_toggle(current).count():
            expect(own_toggle(current)).to_have_attribute("aria-expanded", "true")
        # the generated pages after the last part are outside it, after a separator
        top = toc.locator("ul.bp_tree > li.bp_tree_item")
        for title in ("Dependency Graph", "Blueprint Summary", "Project Stats"):
            expect(top.filter(has_text=title)).to_have_count(1)
        first_after = top.filter(has_text="Dependency Graph")
        assert first_after.evaluate("e => e.previousElementSibling.classList.contains('bp_tree_rule')")
        assert first_after.evaluate("e => e.previousElementSibling.previousElementSibling.classList.contains('bp_tree_part')")
        parts = toc.locator("ul.bp_tree > li.bp_tree_part")
        expect(parts.last.locator("li", has_text="Project Stats")).to_have_count(0)
        # Verso's per-level lists are hidden: each entry is listed once
        for split_toc in toc.locator(".split-toc:not(.book)").all():
            expect(split_toc).to_be_hidden()

    def test_triangle_toggles_without_navigating(self, sidebar_server: str, page: Page):
        errors = record_runtime_errors(page)
        page.goto(sidebar_server + "/Code-Panels/")
        page.evaluate("sessionStorage.clear()")
        page.goto(sidebar_server + "/Code-Panels/")
        toc = page.locator("#toc")
        chapter = tree_item(toc, "External Declaration Heading Repro")
        button = own_toggle(chapter)
        expect(button).to_have_attribute("aria-expanded", "false")
        group_id = button.get_attribute("aria-controls")
        assert group_id and page.locator("#" + group_id).count() == 1
        button.click()
        expect(button).to_have_attribute("aria-expanded", "true")
        expect(page).to_have_url(re.compile(r"/Code-Panels/$"))
        # the sections of a chapter other than the current one can be reached
        link = chapter.locator("a", has_text="Nested External Declaration Panels")
        expect(link).to_be_visible()
        button.click()
        expect(button).to_have_attribute("aria-expanded", "false")
        expect(link).to_be_hidden()
        button.click()
        link.click()
        expect(page).to_have_url(re.compile(r"/External-Declaration-Heading-Repro/Nested-External-Declaration-Panels/"))
        assert_no_runtime_errors(errors)

    def test_keyboard_opens_and_closes_rows(self, sidebar_server: str, page: Page):
        page.goto(sidebar_server + "/Code-Panels/")
        page.evaluate("sessionStorage.clear()")
        page.goto(sidebar_server + "/Code-Panels/")
        toc = page.locator("#toc")
        chapter = tree_item(toc, "Reading Aids")
        button = own_toggle(chapter)
        link = chapter.locator(":scope > .bp_tree_row > a")
        # one Tab stop per row: the triangle is a button for pointers and assistive technology,
        # out of the Tab order, and the row's link opens and closes the row with the arrow keys
        expect(button).to_have_attribute("tabindex", "-1")
        assert button.get_attribute("aria-hidden") is None
        link.focus()
        page.keyboard.press("ArrowRight")
        expect(button).to_have_attribute("aria-expanded", "true")
        page.keyboard.press("ArrowRight")
        expect(tree_item(toc, "A Numbered Section").locator(":scope > .bp_tree_row > a")).to_be_focused()
        page.keyboard.press("ArrowLeft")
        expect(link).to_be_focused()
        page.keyboard.press("ArrowLeft")
        expect(button).to_have_attribute("aria-expanded", "false")
        # Up and Down move between the rows that can be seen; Home and End to the ends
        page.keyboard.press("ArrowDown")
        expect(tree_item(toc, "Dependency Graph").locator(":scope > .bp_tree_row > a")).to_be_focused()
        page.keyboard.press("ArrowUp")
        expect(link).to_be_focused()
        page.keyboard.press("ArrowUp")
        expect(tree_item(toc, "Side-by-Side Runs").locator(":scope > .bp_tree_row > a")).to_be_focused()
        page.keyboard.press("Home")
        expect(toc.locator(".bp_tree_link").first).to_be_focused()
        page.keyboard.press("End")
        expect(tree_item(toc, "Project Stats").locator(":scope > .bp_tree_row > a")).to_be_focused()
        # Tab leaves a row's link for the next row's link, never for a triangle
        link.focus()
        page.keyboard.press("Tab")
        assert page.evaluate("document.activeElement.classList.contains('bp_tree_link')")
        expect(tree_item(toc, "Dependency Graph").locator(":scope > .bp_tree_row > a")).to_be_focused()
        # a focused triangle (as assistive technology focuses it) toggles with Enter and Space
        button.focus()
        page.keyboard.press("Enter")
        expect(button).to_have_attribute("aria-expanded", "true")
        page.keyboard.press("Space")
        expect(button).to_have_attribute("aria-expanded", "false")
        # a visible focus ring on a row reached from the keyboard
        link.focus()
        page.keyboard.press("ArrowDown")
        focused = tree_item(toc, "Dependency Graph").locator(":scope > .bp_tree_row > a")
        assert focused.evaluate("e => getComputedStyle(e).outlineStyle") != "none"
        expect(page).to_have_url(re.compile(r"/Code-Panels/$"))

    def test_open_and_closed_rows_survive_navigation(self, sidebar_server: str, page: Page):
        page.goto(sidebar_server + "/Code-Panels/")
        page.evaluate("sessionStorage.clear()")
        page.goto(sidebar_server + "/Code-Panels/")
        toc = page.locator("#toc")
        part_one = toc.locator("ul.bp_tree > li.bp_tree_part").first
        own_toggle(part_one).click()
        expect(own_toggle(part_one)).to_have_attribute("aria-expanded", "false")
        own_toggle(tree_item(toc, "Reading Aids")).click()
        tree_item(toc, "Inline Hover Previews").locator(":scope > .bp_tree_row > a").click()
        expect(page).to_have_url(re.compile(r"/Inline-Hover-Previews/"))
        toc = page.locator("#toc")
        part_one = toc.locator("ul.bp_tree > li.bp_tree_part").first
        expect(own_toggle(part_one)).to_have_attribute("aria-expanded", "false")
        expect(own_toggle(tree_item(toc, "Reading Aids"))).to_have_attribute("aria-expanded", "true")
        # without storage the page still works, with the default state
        page.add_init_script("Object.defineProperty(window, 'sessionStorage', { get() { throw new Error('blocked'); } })")
        errors = record_runtime_errors(page)
        page.goto(sidebar_server + "/Code-Panels/")
        part_one = page.locator("#toc ul.bp_tree > li.bp_tree_part").first
        expect(own_toggle(part_one)).to_have_attribute("aria-expanded", "true")
        own_toggle(part_one).click()
        expect(own_toggle(part_one)).to_have_attribute("aria-expanded", "false")
        assert_no_runtime_errors(errors)

    def test_current_row_is_scrolled_into_view(self, sidebar_server: str, page: Page):
        page.set_viewport_size({"width": 1280, "height": 420})
        page.goto(sidebar_server + SECTION_PAGE)
        row = page.locator("#toc .bp_tree_row.bp_tree_current")
        box = row.bounding_box()
        assert box is not None and 0 <= box["y"] and box["y"] + box["height"] <= 420, box
        # the page itself is not scrolled
        assert page.evaluate("window.scrollY") == 0

    def test_parts_stand_out_without_scripts(self, sidebar_server: str, browser):
        context = browser.new_context(java_script_enabled=False)
        try:
            page = context.new_page()
            page.goto(sidebar_server + "/Code-Panels/")
            toc = page.locator("#toc")
            expect(toc.locator(".bp_tree")).to_have_count(0)
            part_row = toc.locator(".split-toc.book tr").filter(has=page.locator(".bp_part_label")).first
            expect(part_row).to_be_visible()
            label = part_row.locator(".bp_part_label")
            assert label.evaluate("e => getComputedStyle(e).display") == "block"
            assert label.evaluate("e => getComputedStyle(e).textTransform") == "uppercase"
            assert int(part_row.locator("a").evaluate("e => getComputedStyle(e).fontWeight")) >= 600
            # the chapters after a part are indented; the chapters before the first part are not
            inside = toc.locator(".split-toc.book tr.numbered").filter(has_text="Group Previews")
            before = toc.locator(".split-toc.book tr.numbered").filter(has_text="Code Panels")
            assert float(inside.evaluate("e => parseFloat(getComputedStyle(e).paddingLeft)")) > 0
            assert float(before.evaluate("e => parseFloat(getComputedStyle(e).paddingLeft)")) == 0
        finally:
            context.close()

    def test_tree_on_a_phone(self, sidebar_server: str, page: Page):
        errors = record_runtime_errors(page)
        page.set_viewport_size({"width": 390, "height": 844})
        page.goto(sidebar_server + SECTION_PAGE)
        toc = page.locator("#toc")
        page.locator("#toggle-toc-click").click()
        section = tree_item(toc, "A Numbered Section")
        expect(own_row(section)).to_be_visible()
        assert toc.evaluate("e => e.scrollWidth <= e.clientWidth + 1")
        box = toc.bounding_box()
        assert box is not None and box["x"] + box["width"] <= 391
        chapter = tree_item(toc, "Reading Aids")
        own_toggle(chapter).click()
        expect(own_toggle(chapter)).to_have_attribute("aria-expanded", "false")
        expect(page).to_have_url(re.compile(re.escape(SECTION_PAGE) + "$"))
        assert_no_runtime_errors(errors)

    def test_front_page_marks_home(self, sidebar_server: str, page: Page):
        page.goto(sidebar_server + "/")
        home = page.locator("#toc tr.bp_sidebar_home")
        expect(home).to_have_class(re.compile(r"\bbp_sidebar_current\b"))
        expect(home.locator("a")).to_have_attribute("aria-current", "page")
        expect(page.locator("#toc .bp_tree_current")).to_have_count(0)
        page.goto(sidebar_server + "/Code-Panels/")
        expect(page.locator("#toc tr.bp_sidebar_home")).not_to_have_class(re.compile(r"\bbp_sidebar_current\b"))

    def test_triangles_are_large_enough_to_hit(self, sidebar_server: str, page: Page):
        page.set_viewport_size({"width": 1280, "height": 900})
        page.goto(sidebar_server + SECTION_PAGE)
        toc = page.locator("#toc")
        # a part and chapters with entries below them (sections: in the test of numbers below)
        part = toc.locator("ul.bp_tree > li.bp_tree_part").last
        for item in (part, tree_item(toc, "Reading Aids"), tree_item(toc, "External Declaration Heading Repro")):
            box = own_toggle(item).bounding_box()
            assert box is not None and box["width"] >= 24 and box["height"] >= 24, box
        # a click anywhere in the box toggles: its corner, not only the drawn triangle
        button = own_toggle(tree_item(toc, "External Declaration Heading Repro"))
        before = button.get_attribute("aria-expanded")
        button.click(position={"x": 2, "y": 2})
        expect(button).not_to_have_attribute("aria-expanded", before or "")

    def test_scroll_position_is_kept_across_pages(self, sidebar_server: str, page: Page):
        page.set_viewport_size({"width": 1280, "height": 520})
        page.goto(sidebar_server + "/Code-Panels/")
        page.evaluate("sessionStorage.clear()")
        page.goto(sidebar_server + "/Code-Panels/")
        toc = page.locator("#toc")
        # open every row, so that the list is longer than the window
        page.evaluate(
            """() => { let b; while ((b = document.querySelector("#toc .bp_tree_toggle[aria-expanded='false']"))) b.click(); }"""
        )
        scrolled = page.evaluate(
            """() => { const a = document.querySelector('#toc .bp_tree_link');
                       let box = a.parentElement;
                       while (box && !(['auto', 'scroll'].includes(getComputedStyle(box).overflowY)
                                         && box.scrollHeight > box.clientHeight)) box = box.parentElement;
                       box.scrollTop += 120; return box.scrollTop; }"""
        )
        assert scrolled >= 120
        # a row in view, not the current one: where it is before and after following it
        target = page.evaluate(
            """() => { const links = [...document.querySelectorAll('#toc .bp_tree_link')];
                       const a = links.find((l) => { const r = l.getBoundingClientRect();
                         return r.top > 220 && r.bottom < 480 && !l.closest('.bp_tree_current')
                           && !l.closest('ul[hidden]') && l.querySelector('.bp_tree_title').textContent.trim(); });
                       return [a.querySelector('.bp_tree_title').textContent.trim(), a.getBoundingClientRect().top]; }"""
        )
        title, before = target
        tree_item(toc, title).locator(":scope > .bp_tree_row > a").click()
        page.wait_for_load_state("load")
        toc = page.locator("#toc")
        row = tree_item(toc, title).locator(":scope > .bp_tree_row > a")
        expect(row).to_have_attribute("aria-current", "page")
        after = row.evaluate("e => e.getBoundingClientRect().top")
        assert abs(after - before) <= 2, (title, before, after)

    def test_list_does_not_change_in_view_while_the_outline_loads(self, slow_outline_server: str, page: Page):
        page.set_viewport_size({"width": 1280, "height": 800})
        started = time.time()
        page.goto(slow_outline_server + "/Reading-Aids/", wait_until="domcontentloaded")
        # the page's other scripts do not wait for the outline
        assert time.time() - started < 1.4
        assert page.evaluate("window.versoBlueprintSidebarOutline === undefined")
        book = page.locator("#toc .split-toc.book")
        # until the tree is built, the list is out of sight: nothing is seen moving
        assert book.evaluate("e => getComputedStyle(e).visibility") == "hidden"
        expect(page.locator("#toc .bp_tree")).to_be_visible(timeout=5000)
        assert book.evaluate("e => getComputedStyle(e).visibility") == "visible"
        positions = page.evaluate(
            "() => [...document.querySelectorAll('#toc .bp_tree_title')].map((e) => e.getBoundingClientRect().left)"
        )
        page.wait_for_timeout(300)
        assert positions == page.evaluate(
            "() => [...document.querySelectorAll('#toc .bp_tree_title')].map((e) => e.getBoundingClientRect().left)"
        )

    def test_titles_of_siblings_line_up_whatever_their_numbers(self, sidebar_server: str, page: Page):
        numbers = ["§10.1", "§10.2", "§10.9", "§10.10", "§10.11"]
        outline = {
            "entries": [
                {"title": "Short", "number": "9.", "href": "Code-Panels/#a", "page": "Code-Panels/", "children": []},
                {
                    "title": "Long",
                    "number": "10.",
                    "href": "Reading-Aids/#b",
                    "page": "Reading-Aids/",
                    "children": [
                        {
                            "title": f"Section {n}",
                            "number": n,
                            "href": f"Reading-Aids/#s{i}",
                            "children": [{"title": f"Below {n}", "href": f"Reading-Aids/#t{i}", "children": []}],
                        }
                        for i, n in enumerate(numbers)
                    ],
                },
            ]
        }
        body = "window.versoBlueprintSidebarOutline = " + json.dumps(outline) + ";"
        page.route(
            "**/blueprint-sidebar-outline.js",
            lambda route: route.fulfill(status=200, content_type="text/javascript", body=body),
        )
        page.goto(sidebar_server + "/Reading-Aids/")
        toc = page.locator("#toc")
        lefts = [
            tree_item(toc, f"Section {n}")
            .locator(":scope > .bp_tree_row .bp_tree_title")
            .evaluate("e => e.getBoundingClientRect().left")
            for n in numbers
        ]
        assert max(lefts) - min(lefts) < 0.5, lefts
        chapters = [
            tree_item(toc, t).locator(":scope > .bp_tree_row .bp_tree_title").evaluate("e => e.getBoundingClientRect().left")
            for t in ("Short", "Long")
        ]
        assert abs(chapters[0] - chapters[1]) < 0.5, chapters
        # a section's triangle is as large a target as a chapter's
        box = own_toggle(tree_item(toc, "Section §10.1")).bounding_box()
        assert box is not None and box["width"] >= 24 and box["height"] >= 24, box

    def test_titles_with_lean_code_and_formulas(self, sidebar_server: str, page: Page):
        errors = record_runtime_errors(page)
        page.goto(sidebar_server + "/Group-Previews/")
        toc = page.locator("#toc")
        code_row = tree_item(toc, "Groups Named by", exact=False)
        code = code_row.locator(":scope > .bp_tree_row .bp_tree_title code.hl.lean")
        expect(code).to_contain_text("Nat.succ")
        # the code keeps its highlighting, without the page's hover keys: a hover key in the
        # outline would name an unrelated entry of the site's hover data on another page
        expect(code.locator(".const.token")).to_have_count(1)
        expect(toc.locator(".bp_tree [data-verso-hover], .bp_tree [data-binding]")).to_have_count(0)
        # in the row's colour, which reads on the sidebar
        link_colour = code_row.locator(":scope > .bp_tree_row > a").evaluate("e => getComputedStyle(e).color")
        assert code.locator(".const.token").evaluate("e => getComputedStyle(e).color") == link_colour
        # the formula is drawn, as on the page
        math_row = tree_item(toc, "Statements", exact=False)
        formula = math_row.locator(":scope > .bp_tree_row .bp_tree_title .bp_math")
        expect(formula).to_have_count(1)
        size = formula.bounding_box()
        assert size is not None and size["width"] > 5 and size["height"] > 5
        # every glyph the pictures use is defined on the page
        assert formula.evaluate(
            """e => [...e.querySelectorAll('use')].every((u) =>
                 document.querySelector(u.getAttribute('href') || u.getAttribute('xlink:href')))"""
        )
        # the TeX source is kept for copying, out of sight, as on the page
        source = formula.locator(".bp_math_source")
        if source.count():
            assert source.evaluate("e => getComputedStyle(e).clipPath") != "none"
        assert_no_runtime_errors(errors)

    def test_stored_state_that_is_not_an_object_is_replaced(self, sidebar_server: str, page: Page):
        page.goto(sidebar_server + "/Code-Panels/")
        page.evaluate("sessionStorage.setItem('verso-blueprint-sidebar-tree', '[1, 2]')")
        page.goto(sidebar_server + "/Code-Panels/")
        part_one = page.locator("#toc ul.bp_tree > li.bp_tree_part").first
        expect(own_toggle(part_one)).to_have_attribute("aria-expanded", "true")
        own_toggle(part_one).click()
        page.goto(sidebar_server + "/Code-Panels/")
        part_one = page.locator("#toc ul.bp_tree > li.bp_tree_part").first
        expect(own_toggle(part_one)).to_have_attribute("aria-expanded", "false")
        stored = json.loads(page.evaluate("sessionStorage.getItem('verso-blueprint-sidebar-tree')"))
        assert isinstance(stored, dict) and False in stored.values()


class TestSidebarSinglePage:
    def test_tree_on_a_single_page_site(self, sidebar_single_server: str, page: Page):
        errors = record_runtime_errors(page)
        page.goto(sidebar_single_server + "/")
        toc = page.locator("#toc")
        expect(toc.locator("ul.bp_tree")).to_have_count(1)
        expect(toc.locator("ul.bp_tree > li.bp_tree_part")).to_have_count(2)
        # every entry's link names a place on this page
        hrefs = toc.locator(".bp_tree_link").evaluate_all("(links) => links.map((a) => a.href)")
        assert hrefs
        for href in hrefs:
            assert "#" in href, href
            target = href.split("#", 1)[1]
            assert page.evaluate("(id) => document.getElementById(decodeURIComponent(id)) !== null", target), href
        # following one goes there, and marks it current
        chapter = tree_item(toc, "Reading Aids")
        chapter.locator(":scope > .bp_tree_row > a").click()
        expect(page).to_have_url(re.compile(r"#"))
        page.reload()
        chapter = tree_item(page.locator("#toc"), "Reading Aids")
        expect(own_row(chapter)).to_have_class(re.compile(r"\bbp_tree_current\b"))
        expect(own_toggle(chapter)).to_have_attribute("aria-expanded", "true")
        assert_no_runtime_errors(errors)
