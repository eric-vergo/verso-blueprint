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

    def test_node_without_lean_uses_the_card_in_one_column(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        # `used_proof` (fixture chapter "Preview Relationships") has no `(lean := ...)`: it gets the same
        # card, one full-width column, the heading row with kind, number and the status glyph, and its
        # proof folded inside the card, not a separate block after it.
        errors = record_runtime_errors(page)
        page.set_viewport_size({"width": 1440, "height": 900})
        path = None
        for index in sorted(side_by_side_site_dir.rglob("index.html")):
            if 'data-bp-node="used_proof"' in index.read_text(encoding="utf-8"):
                path = "/" + str(index.parent.relative_to(side_by_side_site_dir)).replace("\\", "/") + "/"
                break
        assert path is not None, "no page with the used_proof node"
        page.goto(side_by_side_server + path)
        node = page.locator('.bp_sbs.bp_sbs_single[data-bp-node="used_proof"]')
        expect(node).to_have_count(1)
        expect(node.locator(".bp_sbs_formal")).to_have_count(0)
        tracks = node.locator(":scope > .bp_sbs_grid").evaluate("e => getComputedStyle(e).gridTemplateColumns")
        assert len(tracks.split()) == 1, tracks
        expect(node.locator(".bp_heading_title_row .bp_status_glyph").first).to_be_visible()
        kind = node.locator(".bp_heading_title_row").first.bounding_box()
        glyph = node.locator(".bp_heading_title_row .bp_status_glyph").first.bounding_box()
        assert kind is not None and glyph is not None
        assert abs(glyph["y"] - kind["y"]) < kind["height"], (kind, glyph)
        proof = node.locator(".bp_sbs_informal > details.bp_kind_proof_wrapper")
        expect(proof).to_have_count(1)
        expect(proof.locator(".bp_caption").first).to_have_text("Proof")
        expect(proof).not_to_have_attribute("open", "")
        assert node.evaluate(
            "n => !(n.nextElementSibling && n.nextElementSibling.getAttribute('data-bp-node') === 'used_proof')"
        )
        assert_no_runtime_errors(errors)

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
        page.wait_for_load_state("networkidle")
        page.evaluate("document.fonts.ready")
        # nothing in a declaration card scrolls sideways or sticks out of its column
        overflowing = page.evaluate(
            """() => [...document.querySelectorAll('.bp_sbs_formal')].flatMap((column) => {
                const edge = column.getBoundingClientRect().right + 1;
                return [...column.querySelectorAll('.bp_decl_source, .bp_decl_source *')].filter((e) => {
                  const style = getComputedStyle(e);
                  const scrolls = /auto|scroll/.test(style.overflowX) && e.scrollWidth > e.clientWidth + 1;
                  const box = e.getBoundingClientRect();
                  // trailing spaces of a wrapped line may hang past the edge, unseen
                  const visible = box.width > 0 && e.textContent.trim() !== '';
                  return scrolls || (visible && box.right > edge);
                }).map((e) => e.className);
              })"""
        )
        assert overflowing == [], overflowing

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
              const bg = parse(getComputedStyle(document.body).backgroundColor);
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

    def test_folded_proof_without_visible_chips_is_one_line_in_a_narrow_card(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        # A proof header whose relation chips are all empty (hidden) must not wrap an empty row under
        # "Proof [show]" when the card is narrow (the empty slot used to keep a second line).
        page.set_viewport_size({"width": 520, "height": 900})
        checked = 0
        for index in sorted(side_by_side_site_dir.rglob("index.html")):
            if "bp_kind_proof_wrapper" not in index.read_text(encoding="utf-8"):
                continue
            page.goto(side_by_side_server + "/" + str(index.parent.relative_to(side_by_side_site_dir)).replace("\\", "/") + "/")
            heights = page.evaluate(
                """() => [...document.querySelectorAll('.bp_sbs_informal > details.bp_kind_proof_wrapper:not([open]) > summary')]
                  .filter((s) => ![...s.querySelectorAll('.bp_extras *')].some((e) => e.getBoundingClientRect().width > 0))
                  .map((s) => [s.getBoundingClientRect().height, s.querySelector('.bp_heading_title_row').getBoundingClientRect().height])"""
            )
            for summary, title in heights:
                assert summary <= title + 2, (index, summary, title)
                checked += 1
        if checked == 0:
            pytest.skip("fixture has no folded proof without visible chips")

    def test_lean_hover_stays_inside_a_narrow_viewport(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        page.set_viewport_size({"width": 560, "height": 800})
        page.goto(side_by_side_server + side_by_side_page_path(side_by_side_site_dir))
        page.wait_for_load_state("networkidle")
        token = page.locator(".bp_sbs_formal .hl.lean [data-verso-hover]").first
        if token.count() == 0:
            pytest.skip("fixture has no hover in the Lean column")
        token.scroll_into_view_if_needed()
        token.hover()
        box = page.locator(".tippy-box[data-theme~='lean']").first
        expect(box).to_be_visible()
        # the box is bounded by the viewport (WebKit otherwise sizes it to its widest line)
        max_width = box.evaluate("e => getComputedStyle(e).maxWidth")
        assert max_width.endswith("px") and float(max_width[:-2]) < page.viewport_size["width"], max_width
        # a long signature, with spaces and as one unbreakable name, wraps inside it
        for text in ["theorem_with_a_long_name " + "(h : Nat → Nat → Nat) " * 12, "a_very_long_identifier_" * 20]:
            page.evaluate(
                """(t) => { const c = document.querySelector(".tippy-box[data-theme~='lean'] .hover-info > code");
                           if (c) c.textContent = t; }""",
                text,
            )
            page.wait_for_timeout(200)
            width = page.evaluate("() => [document.documentElement.scrollWidth, document.documentElement.clientWidth]")
            assert width[0] <= width[1], width
            right = box.evaluate("e => e.getBoundingClientRect().right")
            assert right <= page.viewport_size["width"], right


def runs_page_path(site_dir: Path) -> str:
    for path in sorted(site_dir.rglob("index.html")):
        if 'data-bp-node="runs_first"' in path.read_text(encoding="utf-8"):
            return "/" + str(path.parent.relative_to(site_dir)).replace("\\", "/") + "/"
    raise AssertionError("no page with the runs_first node")


# Geometry of every run on the page: its box, and per node its box, whether it has two columns,
# its divider's x position (or null) and the right edge of its informal column and left edge of
# its Lean column.
_RUN_GEOMETRY_JS = """
() => [...document.querySelectorAll('.bp_sbs_run')].map((run) => {
  const r = run.getBoundingClientRect();
  const nodes = [...run.querySelectorAll(':scope > .bp_sbs')].map((node) => {
    const grid = node.querySelector(':scope > .bp_sbs_grid');
    const g = grid.getBoundingClientRect();
    const before = getComputedStyle(grid, '::before');
    const hasDivider = before.content !== 'none' && before.display !== 'none';
    const informal = grid.querySelector(':scope > .bp_sbs_informal').getBoundingClientRect();
    const formalEl = grid.querySelector(':scope > .bp_sbs_formal');
    const formal = formalEl ? formalEl.getBoundingClientRect() : null;
    return {
      label: node.getAttribute('data-bp-node'),
      top: g.top, bottom: g.bottom,
      divider: hasDivider ? g.left + parseFloat(before.left) : null,
      dividerTop: hasDivider ? g.top + parseFloat(before.top) : null,
      dividerBottom: hasDivider ? g.bottom - parseFloat(before.bottom) : null,
      informalRight: informal.right,
      formalLeft: formal ? formal.left : null,
      border: getComputedStyle(grid).borderTopWidth,
      background: getComputedStyle(grid).backgroundColor,
    };
  });
  return { top: r.top, bottom: r.bottom, nodes };
})
"""

_FIRST_PROSE_SUMMARY = (
    '.bp_sbs[data-bp-node="runs_first"] .bp_sbs_informal > details.bp_kind_proof_wrapper > summary'
)


class TestSideBySideRuns:
    def open_runs(self, page: Page, server: str, site_dir: Path, width: int = 1440) -> None:
        page.set_viewport_size({"width": width, "height": 900})
        page.goto(server + runs_page_path(site_dir))
        page.wait_for_load_state("networkidle")

    def test_one_divider_spans_each_run(self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page):
        errors = record_runtime_errors(page)
        self.open_runs(page, side_by_side_server, side_by_side_site_dir)
        runs = page.evaluate(_RUN_GEOMETRY_JS)
        mine = [run for run in runs if run["nodes"] and run["nodes"][0]["label"] in ("runs_first", "runs_long_proof")]
        # prose between the nodes ends the first run
        assert [[n["label"] for n in run["nodes"]] for run in mine] == [
            ["runs_first", "runs_definition", "runs_lean_only"],
            ["runs_long_proof"],
        ]
        for run in mine:
            nodes = run["nodes"]
            # no card: no border, no background
            assert all(n["border"] == "0px" for n in nodes), nodes
            assert all(n["background"] in ("rgba(0, 0, 0, 0)", "transparent") for n in nodes), nodes
            # one line: the same x everywhere, in the column gap, and the segments meet from the
            # run's top to its bottom
            xs = {round(n["divider"], 1) for n in nodes}
            assert len(xs) == 1 and None not in xs, nodes
            for n in nodes:
                assert n["informalRight"] <= n["divider"] <= n["formalLeft"], n
            assert abs(nodes[0]["dividerTop"] - run["top"]) <= 0.5, (run["top"], nodes[0])
            assert abs(nodes[-1]["dividerBottom"] - run["bottom"]) <= 0.5, (run["bottom"], nodes[-1])
            for above, below in zip(nodes, nodes[1:]):
                assert abs(below["dividerTop"] - above["dividerBottom"]) <= 0.5, (above, below)
        assert_no_runtime_errors(errors)

    def test_narrow_width_stacks_without_divider_or_sideways_scroll(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        for width in (360, 600):
            self.open_runs(page, side_by_side_server, side_by_side_site_dir, width)
            page.locator(_FIRST_PROSE_SUMMARY).click()
            page.wait_for_timeout(400)
            runs = page.evaluate(_RUN_GEOMETRY_JS)
            assert all(n["divider"] is None for run in runs for n in run["nodes"]), width
            scroll = page.evaluate("() => [document.documentElement.scrollWidth, document.documentElement.clientWidth]")
            assert scroll[0] <= scroll[1], (width, scroll)

    def test_one_toggle_opens_prose_and_lean_proofs(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        errors = record_runtime_errors(page)
        self.open_runs(page, side_by_side_server, side_by_side_site_dir)
        node = page.locator('.bp_sbs[data-bp-node="runs_first"]')
        prose = node.locator(".bp_sbs_informal > details.bp_kind_proof_wrapper")
        lean = node.locator(".bp_sbs_formal details.bp_decl_source_proof")
        summary = page.locator(_FIRST_PROSE_SUMMARY)
        expect(node).to_have_attribute("data-bp-proofs-linked", "")
        # the Lean proof's own toggle gives way; the closed Lean proof takes no room
        expect(lean.locator("summary")).to_be_hidden()
        expect(lean).to_be_hidden()
        expect(summary).to_have_attribute("aria-expanded", "false")
        controls = summary.get_attribute("aria-controls")
        assert controls and lean.get_attribute("id") in controls.split()
        summary.focus()
        page.keyboard.press("Enter")
        expect(prose).to_have_attribute("open", "")
        expect(lean).to_have_attribute("open", "")
        expect(summary).to_have_attribute("aria-expanded", "true")
        expect(lean.locator("code.hl.lean.block")).to_be_visible()
        page.wait_for_function("() => !document.querySelector('[data-bp-animating]')")
        assert page.evaluate("() => document.activeElement && document.activeElement.matches('summary')")
        expect(summary).to_be_focused()
        summary.click()
        expect(summary).to_have_attribute("aria-expanded", "false")
        page.wait_for_function("() => !document.querySelector('[data-bp-animating]')")
        expect(prose).not_to_have_attribute("open", "")
        expect(lean).not_to_have_attribute("open", "")
        assert_no_runtime_errors(errors)

    def test_lean_only_node_keeps_its_lean_toggle(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        self.open_runs(page, side_by_side_server, side_by_side_site_dir)
        node = page.locator('.bp_sbs[data-bp-node="runs_lean_only"]')
        expect(node).not_to_have_attribute("data-bp-proofs-linked", "")
        lean = node.locator(".bp_sbs_formal details.bp_decl_source_proof")
        expect(lean.locator("summary")).to_be_visible()
        lean.locator("summary").click()
        expect(lean).to_have_attribute("open", "")
        expect(lean.locator("code.hl.lean.block")).to_be_visible()

    def test_animation_is_capped_and_reversible(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        self.open_runs(page, side_by_side_server, side_by_side_site_dir)
        durations = {}
        for label in ("runs_first", "runs_long_proof"):
            summary = page.locator(
                f'.bp_sbs[data-bp-node="{label}"] .bp_sbs_informal > details.bp_kind_proof_wrapper > summary'
            )
            summary.scroll_into_view_if_needed()
            summary.click()
            durations[label] = page.evaluate(
                f"""() => [...document.querySelectorAll('.bp_sbs[data-bp-node="{label}"] details')]
                      .flatMap((d) => d.getAnimations()).map((a) => a.effect.getTiming().duration)"""
            )
            page.wait_for_function("() => !document.querySelector('[data-bp-animating]')")
        cap = page.evaluate(
            "() => getComputedStyle(document.documentElement).getPropertyValue('--bp-sbs-proof-duration').trim()"
        )
        cap_ms = float(cap[:-2]) if cap.endswith("ms") else float(cap[:-1]) * 1000
        # both proofs of a node move, each for the capped duration, long or short
        for label, values in durations.items():
            assert len(values) >= 2 and all(v == cap_ms for v in values), (label, values, cap)
        # a second press mid-way reverses: the proof ends closed, at its closed height
        details = page.locator('.bp_sbs[data-bp-node="runs_long_proof"] .bp_sbs_informal > details.bp_kind_proof_wrapper')
        first = page.locator('.bp_sbs[data-bp-node="runs_first"] .bp_sbs_informal > details.bp_kind_proof_wrapper')
        summary = details.locator("summary")
        summary.click()
        page.wait_for_timeout(int(cap_ms / 3))
        summary.click()
        page.wait_for_function("() => !document.querySelector('[data-bp-animating]')")
        expect(details).to_have_attribute("open", "")
        summary.click()
        page.wait_for_timeout(int(cap_ms / 3))
        mid = details.evaluate("e => e.getBoundingClientRect().height")
        summary.click()
        page.wait_for_function("() => !document.querySelector('[data-bp-animating]')")
        expect(details).to_have_attribute("open", "")
        full = details.evaluate("e => e.getBoundingClientRect().height")
        assert mid < full, (mid, full)
        assert first.evaluate("e => e.style.height") == ""

    def test_reduced_motion_opens_at_once(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        page.emulate_media(reduced_motion="reduce")
        self.open_runs(page, side_by_side_server, side_by_side_site_dir)
        page.locator(_FIRST_PROSE_SUMMARY).click()
        state = page.evaluate(
            """() => [...document.querySelectorAll('.bp_sbs[data-bp-node="runs_first"] details')]
                  .map((d) => [d.open, d.getAnimations().length, d.hasAttribute('data-bp-animating')])"""
        )
        assert state and all(s == [True, 0, False] for s in state), state

    def test_without_scripts_both_proofs_open_natively(
        self, browser, side_by_side_server: str, side_by_side_site_dir: Path
    ):
        context = browser.new_context(java_script_enabled=False, viewport={"width": 1440, "height": 900})
        try:
            page = context.new_page()
            page.goto(side_by_side_server + runs_page_path(side_by_side_site_dir))
            node = page.locator('.bp_sbs_run > .bp_sbs[data-bp-node="runs_first"]')
            expect(node).to_have_count(1)
            # the generator already placed the proof in the node's informal column
            prose = node.locator(".bp_sbs_informal > details.bp_kind_proof_wrapper")
            lean = node.locator(".bp_sbs_formal details.bp_decl_source_proof")
            expect(prose).to_have_count(1)
            expect(lean.locator("summary")).to_be_visible()
            prose.locator("summary").first.click()
            expect(prose).to_have_attribute("open", "")
            lean.locator("summary").click()
            expect(lean).to_have_attribute("open", "")
            expect(lean.locator("code.hl.lean.block")).to_be_visible()
        finally:
            context.close()

    def test_deep_link_into_a_proof_opens_it_and_marks_the_node(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        self.open_runs(page, side_by_side_server, side_by_side_site_dir)
        proof_id = page.locator(
            '.bp_sbs[data-bp-node="runs_long_proof"] .bp_sbs_informal > details.bp_kind_proof_wrapper'
        ).get_attribute("id")
        assert proof_id
        page.goto(side_by_side_server + runs_page_path(side_by_side_site_dir) + "#" + proof_id)
        page.wait_for_load_state("networkidle")
        node = page.locator('.bp_sbs[data-bp-node="runs_long_proof"]')
        expect(node.locator(".bp_sbs_informal > details.bp_kind_proof_wrapper")).to_have_attribute("open", "")
        expect(node.locator(".bp_sbs_formal details.bp_decl_source_proof")).to_have_attribute("open", "")
        tint = node.locator(":scope > .bp_sbs_grid").evaluate("e => getComputedStyle(e).backgroundColor")
        assert tint not in ("rgba(0, 0, 0, 0)", "transparent"), tint
        other = page.locator('.bp_sbs[data-bp-node="runs_first"] > .bp_sbs_grid').evaluate(
            "e => getComputedStyle(e).backgroundColor"
        )
        assert other in ("rgba(0, 0, 0, 0)", "transparent"), other


# The id of the graph node whose label is `label`, from the page's graph data.
_GRAPH_NODE_ID_JS = """
label => {
  const data = JSON.parse(document.querySelector('script.bp-graph-data').textContent);
  const node = (data.nodes || []).find(n => n.label === label);
  if (!node) return '';
  const pairs = (data.variants[0] || {}).previewKeyByNodeId || [];
  const pair = pairs.find(p => p[1] === node.previewKey);
  return pair ? pair[0] : '';
}
"""


def _open_graph(page: Page, server: str, fragment: str = "") -> None:
    page.set_viewport_size({"width": 1440, "height": 900})
    page.goto(server + "/Dependency-Graph/" + fragment)
    page.locator(".bp_graph_canvas svg g.node").first.wait_for()


def _click_graph_node(page: Page, label: str) -> None:
    node_id = page.evaluate(_GRAPH_NODE_ID_JS, label)
    assert node_id, f"no graph node {label}"
    page.locator(f'[id="{node_id}"]').first.dispatch_event("click")


class TestGraphNodeView:
    def test_node_click_shows_statement_beside_lean(self, side_by_side_server: str, page: Page):
        errors = record_runtime_errors(page)
        _open_graph(page, side_by_side_server)
        _click_graph_node(page, "panel_external_theorem")
        view = page.locator('.bp_graph_preview .bp_node_view[data-bp-node-view="panel_external_theorem"]')
        expect(view).to_be_visible()
        expect(view).to_have_attribute("data-bp-node-view-layout", "both")
        expect(page.locator(".bp_graph_preview")).to_have_attribute("data-bp-preview-size", "node")
        left = view.locator(".bp_sbs_informal").bounding_box()
        right = view.locator(".bp_sbs_formal").bounding_box()
        assert left is not None and right is not None
        assert right["x"] > left["x"] + left["width"] - 1
        expect(view.locator(".bp_sbs_formal .bp_decl_source code.hl.lean")).not_to_have_count(0)
        expect(view.locator(".bp_node_view_header .bp_status_glyph")).to_be_visible()
        assert page.url.endswith("#node=panel_external_theorem"), page.url
        assert_no_runtime_errors(errors)

    def test_node_without_prose_shows_lean_alone(self, side_by_side_server: str, page: Page):
        # `panel_docstring_target` comes from `@[blueprint]` on declarations without docstrings
        _open_graph(page, side_by_side_server)
        _click_graph_node(page, "panel_docstring_target")
        view = page.locator('.bp_graph_preview .bp_node_view[data-bp-node-view="panel_docstring_target"]')
        expect(view).to_have_attribute("data-bp-node-view-layout", "lean")
        expect(view.locator(".bp_sbs_informal")).to_have_count(0)
        grid = view.locator(".bp_sbs_grid").bounding_box()
        formal = view.locator(".bp_sbs_formal").bounding_box()
        assert grid is not None and formal is not None
        # full width: the Lean column fills the card, less its padding
        assert formal["width"] > grid["width"] * 0.9, (grid, formal)

    def test_url_reopens_the_view_and_links_switch_nodes(self, side_by_side_server: str, page: Page):
        _open_graph(page, side_by_side_server, "#node=used_target")
        view = page.locator('.bp_graph_preview:not([hidden]) .bp_node_view')
        expect(view).to_have_attribute("data-bp-node-view", "used_target")
        link = view.locator("[data-bp-node-link]").first
        target = link.get_attribute("data-bp-node-link")
        assert target
        link.click()
        expect(page.locator(".bp_graph_preview .bp_node_view")).to_have_attribute("data-bp-node-view", target)
        page.wait_for_function("t => decodeURIComponent(location.hash) === '#node=' + t", arg=target)
        page.locator(".bp_graph_preview_close").click()
        expect(page.locator(".bp_graph_preview")).to_be_hidden()
        page.wait_for_function("() => location.hash === '#node='")

    def test_lean_hovers_work_in_the_view(self, side_by_side_server: str, page: Page):
        _open_graph(page, side_by_side_server)
        _click_graph_node(page, "panel_external_theorem")
        token = page.locator(".bp_graph_preview .bp_sbs_formal .hl.lean [data-verso-hover]").first
        token.hover()
        expect(page.locator(".tippy-box").first).to_be_visible()

    def test_view_follows_the_dark_theme(self, side_by_side_server: str, page: Page):
        page.emulate_media(color_scheme="dark")
        _open_graph(page, side_by_side_server)
        _click_graph_node(page, "panel_external_theorem")
        grid = page.locator(".bp_graph_preview .bp_node_view .bp_sbs_grid")
        expect(grid).to_be_visible()
        rgb = grid.evaluate("e => getComputedStyle(e).backgroundColor")
        channels = [int(c) for c in rgb[rgb.index("(") + 1 : rgb.index(")")].split(",")[:3]]
        assert sum(channels) / 3 < 90, rgb
