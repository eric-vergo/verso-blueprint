"""Browser checks for the side-by-side node layout (`--side-by-side`)."""

import subprocess
import sys
from pathlib import Path

import pytest
from playwright.sync_api import Page, expect

from scripts.blueprint_harness_paths import canonical_test_blueprint_output_dir
from scripts.blueprint_harness_utils import lean_low_priority_command
from support import PACKAGE_ROOT, assert_no_runtime_errors, find_free_port, record_runtime_errors, wait_for_server


@pytest.fixture(scope="session")
def side_by_side_site_dir() -> Path:
    output_dir = canonical_test_blueprint_output_dir("preview_runtime_showcase", Path(__file__))
    output_dir = output_dir.parent / (output_dir.name + "-side-by-side")
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
            "--side-by-side",
        ),
        cwd=project_dir,
        check=True,
    )
    return output_dir / "html-multi"


@pytest.fixture(scope="session")
def side_by_side_server(side_by_side_site_dir: Path):
    port = find_free_port()
    proc = subprocess.Popen(
        [sys.executable, "-m", "http.server", str(port), "--bind", "127.0.0.1"],
        cwd=side_by_side_site_dir,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    url = f"http://127.0.0.1:{port}"
    wait_for_server(url, proc)
    yield url
    proc.terminate()
    proc.wait()


def side_by_side_page_path(site_dir: Path) -> str:
    for path in sorted(site_dir.rglob("index.html")):
        if 'class="bp_decl_source ' in path.read_text(encoding="utf-8"):
            return "/" + str(path.parent.relative_to(site_dir)).replace("\\", "/") + "/"
    raise AssertionError("no page with a declaration source card")


class TestSideBySideRuntime:
    def test_nodes_render_in_two_columns_by_default(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        errors = record_runtime_errors(page)
        page.set_viewport_size({"width": 1440, "height": 900})
        page.goto(side_by_side_server + side_by_side_page_path(side_by_side_site_dir))
        expect(page.locator("html")).to_have_attribute("data-bp-style", "sbs")
        node = page.locator(".bp_sbs:has(.bp_decl_source)").first
        informal = node.locator(".bp_sbs_informal").first
        formal = node.locator(".bp_sbs_formal").first
        node.scroll_into_view_if_needed()
        left = informal.bounding_box()
        right = formal.bounding_box()
        assert left is not None and right is not None
        assert right["x"] > left["x"] + left["width"] - 1
        # the status glyph sits in the title row
        expect(node.locator(".bp_heading_title_row .bp_status_glyph").first).to_be_visible()
        assert_no_runtime_errors(errors)

    def test_lean_proof_toggle_folds_and_unfolds(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        page.goto(side_by_side_server + side_by_side_page_path(side_by_side_site_dir))
        proof = page.locator(".bp_decl_source_proof").first
        if proof.count() == 0:
            pytest.skip("fixture has no theorem-like declaration source")
        expect(proof).not_to_have_attribute("open", "")
        proof.locator("summary").click()
        expect(proof).to_have_attribute("open", "")
        expect(proof.locator("code.hl.lean.block")).to_be_visible()
        proof.locator("summary").click()
        expect(proof).not_to_have_attribute("open", "")

    def test_informal_proof_is_attached_and_folded(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        page.goto(side_by_side_server + side_by_side_page_path(side_by_side_site_dir))
        attached = page.locator(".bp_sbs_informal > details.bp_kind_proof_wrapper")
        if attached.count() == 0:
            pytest.skip("fixture has no proof directly after a side-by-side node")
        proof = attached.first
        expect(proof.locator(".bp_caption").first).to_have_text("Proof")
        expect(proof).not_to_have_attribute("open", "")
        proof.locator("summary").first.click()
        expect(proof).to_have_attribute("open", "")

    def test_narrow_viewport_stacks_columns(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        page.set_viewport_size({"width": 640, "height": 900})
        page.goto(side_by_side_server + side_by_side_page_path(side_by_side_site_dir))
        node = page.locator(".bp_sbs:has(.bp_decl_source)").first
        node.scroll_into_view_if_needed()
        left = node.locator(".bp_sbs_informal").first.bounding_box()
        right = node.locator(".bp_sbs_formal").first.bounding_box()
        assert left is not None and right is not None
        assert right["y"] >= left["y"] + left["height"] - 1

    def test_other_style_stacks_columns(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        page.set_viewport_size({"width": 1440, "height": 900})
        page.goto(side_by_side_server + side_by_side_page_path(side_by_side_site_dir))
        page.select_option("#bp-style-select", "modern")
        expect(page.locator("html")).to_have_attribute("data-bp-style", "modern")
        node = page.locator(".bp_sbs:has(.bp_decl_source)").first
        node.scroll_into_view_if_needed()
        left = node.locator(".bp_sbs_informal").first.bounding_box()
        right = node.locator(".bp_sbs_formal").first.bounding_box()
        assert left is not None and right is not None
        assert right["y"] >= left["y"] + left["height"] - 1

    def test_typography_and_quiet_header_meta(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        page.set_viewport_size({"width": 1440, "height": 900})
        page.goto(side_by_side_server + side_by_side_page_path(side_by_side_site_dir))
        node = page.locator(".bp_sbs:has(.bp_decl_source)").first
        style = lambda sel, prop: node.locator(sel).first.evaluate(f"e => getComputedStyle(e).{prop}")
        # one serif text face for the node heading and the statement, upright
        heading_font = style(".bp_heading .bp_caption", "fontFamily")
        assert heading_font == style(".bp_content", "fontFamily")
        assert "serif" in heading_font and "sans-serif" not in heading_font
        assert style(".bp_content", "fontStyle") == "normal"
        # code in a monospace face
        assert "mono" in style(".bp_decl_source code", "fontFamily").lower()
        # zero-count relation chips are hidden
        for chip in page.locator(".bp_sbs_informal .bp_relation_chip_empty").all():
            expect(chip).to_be_hidden()

    def test_first_code_line_shares_the_title_baseline(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        page.set_viewport_size({"width": 1440, "height": 900})
        page.goto(side_by_side_server + side_by_side_page_path(side_by_side_site_dir))
        node = page.locator(".bp_sbs:has(.bp_decl_source)").first
        node.scroll_into_view_if_needed()
        # bottoms of the first line boxes, measured on zero-width probes at the baseline
        baseline = """e => {
          const probe = document.createElement('span');
          probe.style.cssText = 'display:inline-block;width:0;height:0;vertical-align:baseline';
          e.prepend(probe);
          const y = probe.getBoundingClientRect().top;
          probe.remove();
          return y;
        }"""
        title_y = node.locator(".bp_heading_title_row .bp_caption").first.evaluate(baseline)
        code_y = node.locator(".bp_decl_source .bp_code_line").first.evaluate(baseline)
        assert abs(title_y - code_y) <= 2, (title_y, code_y)

    def test_long_signatures_wrap_without_scrolling(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        page.set_viewport_size({"width": 1100, "height": 900})
        page.goto(side_by_side_server + side_by_side_page_path(side_by_side_site_dir))
        overflowing = page.evaluate(
            """() => [...document.querySelectorAll('.bp_sbs_formal, .bp_decl_source code')]
                .filter((e) => e.scrollWidth > e.clientWidth + 1).length"""
        )
        assert overflowing == 0

    def test_status_legend_lists_every_glyph(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        page.goto(side_by_side_server + side_by_side_page_path(side_by_side_site_dir))
        legend = page.locator(".bp_status_legend")
        expect(legend).to_have_count(1)
        expect(legend).not_to_have_attribute("open", "")
        legend.locator("summary").click()
        for glyph in ["✓", "◐", "⚠", "✗", "○"]:
            expect(legend.locator("dt", has_text=glyph)).to_be_visible()
        title = page.locator(".bp_sbs .bp_status_glyph").first.get_attribute("title")
        assert title and "(" in title

    def test_dark_code_tokens_are_readable(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        page.emulate_media(color_scheme="dark")
        page.goto(side_by_side_server + side_by_side_page_path(side_by_side_site_dir))
        result = page.evaluate(
            """() => {
              const parse = (c) => { const p = c.match(/[\\d.]+/g).map(Number); return { r: p[0], g: p[1], b: p[2], a: p.length > 3 ? p[3] : 1 }; };
              const lum = (c) => { const f = (v) => { v /= 255; return v <= 0.03928 ? v / 12.92 : Math.pow((v + 0.055) / 1.055, 2.4); }; return 0.2126 * f(c.r) + 0.7152 * f(c.g) + 0.0722 * f(c.b); };
              const card = document.querySelector('.bp_sbs_grid');
              const bg = parse(getComputedStyle(card).backgroundColor);
              const tokens = [...document.querySelectorAll('.bp_sbs_formal .hl.lean .token')]
                .filter((el) => el.textContent.trim())
                .map((el) => {
                  const [x, y] = [lum(parse(getComputedStyle(el).color)), lum(bg)].sort((p, q) => q - p);
                  return [el.className, (x + 0.05) / (y + 0.05)];
                });
              return { dark: lum(bg) < 0.05, tokens };
            }"""
        )
        if not result["dark"]:
            pytest.skip("no dark theme on this branch")
        assert result["tokens"]
        failing = [t for t in result["tokens"] if t[1] < 4.5]
        assert not failing, failing
