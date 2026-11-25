"""Browser checks for the side-by-side node layout (`--side-by-side`)."""

import re
import shutil
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
    # start empty, so the checks see only what this build writes
    if output_dir.exists():
        shutil.rmtree(output_dir)
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


def test_blueprint_site_ships_no_graph_libraries(side_by_side_site_dir: Path):
    """The dependency graph is drawn when the site is built, so the site has no graph library."""
    assert not (side_by_side_site_dir / "-verso-data" / "vendor").exists()
    assert (side_by_side_site_dir / "-verso-data" / "blueprint-graph").is_dir()


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
        for glyph in ["✓", "◇", "⊘", "◐", "⚠", "◌", "✗", "○"]:
            expect(legend.locator("dt", has_text=glyph)).to_be_visible()
        # the mark's title says what was checked, in words
        title = page.locator(".bp_sbs .bp_status_glyph").first.get_attribute("title")
        assert title and "Lean" in title and len(title.split()) >= 3

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

# The vertical space between the visible content of consecutive nodes of the run that holds the
# node labelled `label`: from the bottom of one node's columns to the top of the next one's.
_RUN_NODE_GAPS_JS = """
(label) => {
  const run = document.querySelector(`.bp_sbs_run:has(> .bp_sbs[data-bp-node="${label}"])`);
  const extent = (node) => {
    const cols = [...node.querySelectorAll(':scope > .bp_sbs_grid > :is(.bp_sbs_informal, .bp_sbs_formal)')]
      .map((c) => c.getBoundingClientRect()).filter((r) => r.height > 0);
    return [Math.min(...cols.map((r) => r.top)), Math.max(...cols.map((r) => r.bottom))];
  };
  const nodes = [...run.querySelectorAll(':scope > .bp_sbs')].map(extent);
  return nodes.slice(1).map((n, i) => n[0] - nodes[i][1]);
}
"""

_FIRST_PROSE_SUMMARY = (
    '.bp_sbs[data-bp-node="runs_first"] .bp_sbs_informal > details.bp_kind_proof_wrapper > summary'
)


class TestSideBySideRuns:
    def open_runs(self, page: Page, server: str, site_dir: Path, width: int = 1440) -> None:
        page.set_viewport_size({"width": width, "height": 900})
        page.goto(server + runs_page_path(site_dir))
        page.wait_for_load_state("networkidle")

    def test_each_node_has_its_own_divider(self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page):
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
            # the same x everywhere, in the column gap; each divider is as tall as its own node
            # and the dividers of consecutive nodes are apart
            xs = {round(n["divider"], 1) for n in nodes}
            assert len(xs) == 1 and None not in xs, nodes
            for n in nodes:
                assert n["informalRight"] <= n["divider"] <= n["formalLeft"], n
            for n in nodes:
                assert abs(n["dividerTop"] - n["top"]) <= 0.5, n
                assert abs(n["dividerBottom"] - n["bottom"]) <= 0.5, n
            assert abs(nodes[0]["dividerTop"] - run["top"]) <= 0.5, (run["top"], nodes[0])
            assert abs(nodes[-1]["dividerBottom"] - run["bottom"]) <= 0.5, (run["bottom"], nodes[-1])
            for above, below in zip(nodes, nodes[1:]):
                assert below["dividerTop"] - above["dividerBottom"] >= 40, (above, below)
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
        # the Lean proof's own (hidden) toggle says it is open too
        expect(lean.locator(":scope > summary")).to_have_attribute("aria-expanded", "true")
        expect(lean.locator("code.hl.lean.block")).to_be_visible()
        page.wait_for_function("() => !document.querySelector('[data-bp-animating]')")
        assert page.evaluate("() => document.activeElement && document.activeElement.matches('summary')")
        expect(summary).to_be_focused()
        summary.click()
        expect(summary).to_have_attribute("aria-expanded", "false")
        page.wait_for_function("() => !document.querySelector('[data-bp-animating]')")
        expect(prose).not_to_have_attribute("open", "")
        expect(lean).not_to_have_attribute("open", "")
        expect(lean.locator(":scope > summary")).to_have_attribute("aria-expanded", "false")
        assert_no_runtime_errors(errors)

    @pytest.mark.parametrize("style", [None, "sbs", "blueprint", "modern", "bold"])
    def test_nodes_of_a_run_are_spaced_in_every_style(
        self, style, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        self.open_runs(page, side_by_side_server, side_by_side_site_dir)
        page.evaluate(
            "(s) => s === null ? document.documentElement.removeAttribute('data-bp-style')"
            "                  : document.documentElement.setAttribute('data-bp-style', s)",
            style,
        )
        gaps = page.evaluate(_RUN_NODE_GAPS_JS, "runs_first")
        assert len(gaps) >= 2, gaps
        # the nodes never touch: the node gap lies between one node's content and the next
        assert all(gap >= 40 for gap in gaps), (style, gaps)

    def test_print_spaces_nodes_once_and_drops_the_target_tint(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        self.open_runs(page, side_by_side_server, side_by_side_site_dir)
        proof_id = page.locator(
            '.bp_sbs[data-bp-node="runs_definition"] .bp_sbs_informal [id]'
        ).first.get_attribute("id") or "runs_definition"
        page.goto(side_by_side_server + runs_page_path(side_by_side_site_dir) + "#" + proof_id)
        page.wait_for_load_state("networkidle")
        page.emulate_media(media="print")
        state = page.evaluate(
            """() => {
              const run = document.querySelector('.bp_sbs_run:has(> .bp_sbs[data-bp-node="runs_first"])');
              const grids = [...run.querySelectorAll(':scope > .bp_sbs > .bp_sbs_grid')];
              const rem = parseFloat(getComputedStyle(document.documentElement).fontSize);
              const target = run.querySelector(':scope > .bp_sbs:is(:target, :has(:target)) > .bp_sbs_grid');
              return {
                padding: grids.map((g) => [getComputedStyle(g).paddingTop, getComputedStyle(g).paddingBottom]),
                gaps: grids.slice(1).map((g, i) => g.getBoundingClientRect().top - grids[i].getBoundingClientRect().bottom),
                rem,
                target: target && [getComputedStyle(target).backgroundColor, getComputedStyle(target).boxShadow],
              };
            }"""
        )
        assert all(p == ["0px", "0px"] for p in state["padding"]), state
        assert all(abs(gap - state["rem"]) <= 0.5 for gap in state["gaps"]), state
        assert state["target"] is not None, state
        assert state["target"][0] in ("rgba(0, 0, 0, 0)", "transparent") and state["target"][1] == "none", state

    def test_malformed_fragment_leaves_the_page_script_running(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        errors = record_runtime_errors(page)
        page.set_viewport_size({"width": 1440, "height": 900})
        page.goto(side_by_side_server + runs_page_path(side_by_side_site_dir) + "#%E0%A4%A")
        page.wait_for_load_state("networkidle")
        # the steps after the deep link ran: the status legend and the fitted display math
        expect(page.locator(".bp_status_legend")).to_have_count(1)
        expect(page.locator('.bp_sbs[data-bp-node="runs_first"]')).to_have_attribute("data-bp-proofs-linked", "")
        page.evaluate("() => { window.location.hash = '%E0%A4%A'; }")
        page.wait_for_timeout(100)
        assert not [e for e in errors if "URIError" in e], errors
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

    def test_hidden_page_opens_at_once_and_settles(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        # a page that is not visible has nothing to animate (and its animation clock may not run)
        self.open_runs(page, side_by_side_server, side_by_side_site_dir)
        summary = page.locator(_FIRST_PROSE_SUMMARY)
        page.evaluate("() => Object.defineProperty(document, 'visibilityState', { value: 'hidden', configurable: true })")
        summary.click()
        state = page.evaluate(
            """() => [...document.querySelectorAll('.bp_sbs[data-bp-node="runs_first"] details')]
                  .map((d) => [d.open, d.getAnimations().length])"""
        )
        assert state and all(s == [True, 0] for s in state), state
        # visible again, a closing runs; hidden mid-way, it settles closed at once
        page.evaluate("() => { delete document.visibilityState; }")
        assert page.evaluate("() => document.visibilityState") == "visible"
        summary.click()
        page.evaluate(
            """() => { Object.defineProperty(document, 'visibilityState', { value: 'hidden', configurable: true });
                       document.dispatchEvent(new Event('visibilitychange')); }"""
        )
        state = page.evaluate(
            """() => [...document.querySelectorAll('.bp_sbs[data-bp-node="runs_first"] details')]
                  .map((d) => [d.open, d.hasAttribute('data-bp-animating'), d.getAnimations().length])"""
        )
        assert state and all(s == [False, False, 0] for s in state), state

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


# Panels a reader opens with the pointer or the keyboard: relation panels, Lean summaries, inline
# previews. Each visible one with its box, and whether it holds the focused element.
_OPEN_PANELS_JS = """() => {
    const vw = window.innerWidth;
    const main = document.querySelector("main");
    const mainLeft = main ? main.getBoundingClientRect().left : 0;
    const panels = [];
    const selector = ".bp_relation_panel, .bp_preview_panel, .bp_inline_preview_panel, .bp_code_hover";
    for (const el of document.querySelectorAll(selector)) {
        const cs = getComputedStyle(el);
        if (cs.display === "none" || cs.visibility === "hidden" || el.hidden) continue;
        const r = el.getBoundingClientRect();
        if (r.width < 2 || r.height < 2) continue;
        panels.push({ cls: el.className, left: r.left, right: r.right, width: r.width,
                      fixed: cs.position === "fixed",
                      holdsFocus: el.contains(document.activeElement) });
    }
    const a = document.activeElement;
    const ar = a && a !== document.body ? a.getBoundingClientRect() : null;
    return { vw, mainLeft, panels, active: a ? a.tagName : "",
             activeBox: ar && ar.width > 0 ? { left: ar.left, right: ar.right } : null };
}"""


class TestReadingAids:
    """Popovers, numbers, labels and links as a reader of the side-by-side site meets them."""

    @pytest.mark.parametrize("width", (360, 768, 1440))
    @pytest.mark.parametrize("path", ("/Core-Previews/", "/Preview-Relationships/", "/Reading-Aids/"))
    def test_keyboard_popovers_close_and_stay_in_view(
        self, side_by_side_server: str, page: Page, width: int, path: str
    ):
        errors = record_runtime_errors(page)
        page.set_viewport_size({"width": width, "height": 900})
        page.goto(side_by_side_server + path)
        page.wait_for_load_state("networkidle")
        for step in range(140):
            page.keyboard.press("Tab")
            # less than the delay a pointer gets to travel from a trigger to its panel
            page.wait_for_timeout(40)
            state = page.evaluate(_OPEN_PANELS_JS)
            if state["active"] == "BODY":
                assert not state["panels"], (step, state)
                break
            panels = state["panels"]
            # one popover at a time, besides those that hold the focus (opened from inside)
            unrelated = [p for p in panels if not p["holdsFocus"]]
            assert len(unrelated) <= 1, (step, state)
            for p in panels:
                assert p["left"] >= -0.5 and p["right"] <= state["vw"] + 0.5, (step, p, state["vw"])
                # a popover inside the page is not hidden under the table of contents beside it
                if not p["fixed"] and p["width"] <= state["vw"] - state["mainLeft"] - 16:
                    assert p["left"] >= state["mainLeft"] - 0.5, (step, p, state["mainLeft"])
            box = state["activeBox"]
            if box is not None:
                # nothing the keyboard reaches is off the side of the screen
                assert box["left"] >= -0.5 and box["right"] <= state["vw"] + 0.5, (step, state)
        assert_no_runtime_errors(errors)

    def test_lean_summary_is_headed_by_the_statement_and_explains_the_marks(
        self, side_by_side_server: str, page: Page
    ):
        page.set_viewport_size({"width": 1440, "height": 900})
        page.goto(side_by_side_server + "/Reading-Aids/")
        trigger = page.locator(".bp_code_summary_preview_wrap").first
        trigger.hover()
        panel = page.locator(".bp_code_summary_preview_panel:not([hidden])")
        expect(panel).to_be_visible()
        expect(panel.locator(".bp_code_summary_preview_title")).to_have_text(re.compile(r"^Theorem \d+\.1$"))
        expect(panel.locator("a.bp_meaning_link")).to_have_attribute("href", "Project-Stats/#bp-what-this-means")

    def test_statements_carry_no_unchecked_line(self, side_by_side_server: str, page: Page):
        """A statement written in the Blueprint has no line about its source or what was checked;
        the status legend and the Project Stats page still say what no mark is about."""
        for path in ("/Reading-Aids/", "/Core-Previews/", "/Preview-Relationships/"):
            page.goto(side_by_side_server + path)
            expect(page.locator(".bp_sbs").first).to_be_attached()
            expect(page.locator(".bp_statement_source")).to_have_count(0)
            text = page.locator("main").inner_text()
            assert "Informal statement from" not in text, path
            assert "not checked against the Lean statement" not in text, path
        page.goto(side_by_side_server + "/Reading-Aids/")
        legend = page.locator(".bp_status_legend_note")
        expect(legend).to_contain_text("No tool checks that an informal statement says the same")
        page.goto(side_by_side_server + "/Project-Stats/#bp-what-this-means")
        expect(page.locator("#bp-what-this-means")).to_be_visible()

    def test_proof_declarations_have_no_panel(self, side_by_side_server: str, page: Page):
        """A proof with attached Lean declarations shows no panel of them, on the page or in a
        hover preview of the node, while the node's data and status still count them."""
        page.set_viewport_size({"width": 1440, "height": 900})
        page.goto(side_by_side_server + "/Reading-Aids/")
        page.evaluate("() => document.querySelectorAll('details').forEach(d => d.open = true)")
        proof = page.locator("[data-bp-facet='proof'][data-bp-node='aids_first']")
        expect(proof).to_have_count(1)
        assert "aidLongSignature" in (proof.get_attribute("data-lean-decls") or "")
        expect(page.get_by_text("Lean declarations attached to this proof")).to_have_count(0)
        expect(page.locator("[data-lean-decl$='aidLongSignature']")).to_have_count(0)
        assert "theorem aidLongSignature" not in page.locator("main").inner_text()
        # a node whose statement's declaration is complete and whose proof's declaration has a
        # sorry is marked incomplete, and its page shows no panel either: the hidden declaration
        # still counts
        page.goto(side_by_side_server + "/Reading-Aids/A-Numbered-Section/")
        glyph = page.locator(".bp_sbs[data-bp-node='aids_sectioned'] .bp_status_glyph").first
        expect(glyph).to_have_class(re.compile(r"\bbp_status_glyph_partial\b"))
        expect(page.get_by_text("Lean declarations attached to this proof")).to_have_count(0)
        expect(page.locator("[data-lean-decl$='aidOpen']")).to_have_count(0)
        # the preview data keeps the proof facet's declarations
        entry = page.evaluate(
            """async () => {
                const manifest = await (await fetch('-verso-data/blueprint-manifest.json')).json();
                return manifest.previews.find((e) => e.key === 'aids_first--proof');
            }"""
        )
        decls = [d["canonical"] for d in entry["codeData"]["externalDecls"]]
        assert decls == ["PreviewRuntimeShowcase.ReadingAidDecls.aidLongSignature"], decls
        # a hover preview of the node (from its graph node view and from a link to it)
        page.goto(side_by_side_server + "/Dependency-Graph/#node=aids_first", wait_until="domcontentloaded")
        page.wait_for_selector(".bp_graph_preview .bp_node_view", timeout=60000)
        view = page.locator(".bp_graph_preview .bp_node_view")
        assert "Lean declarations attached to this proof" not in view.inner_text()

    def test_every_surface_counts_the_open_proof_declaration(
        self, side_by_side_server: str, page: Page
    ):
        """`aids_sectioned`: its statement's declaration is complete, its proof's has a sorry. The
        heading, its Lean chip, the chip of a placement of the node, the graph's tooltip and
        accessible name and the node view all show it incomplete, and the chip's summary and the
        node view list the proof's declaration with its status."""
        page.set_viewport_size({"width": 1440, "height": 900})
        page.goto(side_by_side_server + "/Reading-Aids/A-Numbered-Section/")
        node = page.locator(".bp_sbs[data-bp-node='aids_sectioned']").first
        expect(node.locator(".bp_status_glyph").first).to_have_class(
            re.compile(r"\bbp_status_glyph_partial\b"))
        chip = node.locator(".bp_code_link_status").first
        expect(chip).to_have_class(re.compile(r"\bbp_code_link_status_warning\b"))
        placement = page.locator("[data-bp-blueprint-node][data-bp-label='aids_sectioned']")
        expect(placement.locator(".bp_code_link_status_warning")).to_have_count(1)
        # the chip's summary: the statement's declaration, then the proof's with its status
        node.locator(".bp_code_summary_preview_wrap").first.hover()
        panel = page.locator(".bp_code_summary_preview_panel:not([hidden])")
        expect(panel).to_be_visible()
        expect(panel).to_contain_text("aidSectioned")
        expect(panel).to_contain_text("Attached to the proof")
        row = panel.locator(".bp_code_decl_item", has_text="aidOpen")
        expect(row).to_have_count(1)
        expect(row.locator(".bp_code_decl_status")).to_contain_text("sorry")
        # the graph's words and the node view
        page.goto(side_by_side_server + "/Dependency-Graph/#node=aids_sectioned",
                  wait_until="domcontentloaded")
        graph_node = page.locator(".bp_graph_canvas svg g.node[id='bp-node-aids-005Fsectioned']")
        expect(graph_node).to_have_count(1)
        assert "Lean code incomplete" in (graph_node.get_attribute("aria-label") or "")
        page.wait_for_selector(".bp_graph_preview .bp_node_view", timeout=60000)
        view = page.locator(".bp_graph_preview .bp_node_view")
        expect(view.locator(".bp_node_view_header .bp_status_glyph_partial")).to_have_count(1)
        expect(view.locator(".bp_node_view_proof_decls")).to_contain_text("Attached to the proof")
        expect(view.locator(".bp_node_view_proof_decl", has_text="aidOpen")).to_have_count(1)

    def test_a_statement_without_lean_code_is_not_complete(self, side_by_side_server: str, page: Page):
        """`aids_proof_only`: its statement has no Lean declaration and its proof's declaration is
        complete. Its heading shows no Lean declaration, its chip says there is no Lean statement
        and lists the proof's declaration, the graph draws it as not formalized and says so, and
        the summary's link to the declaration leads to the node."""
        page.set_viewport_size({"width": 1440, "height": 900})
        page.goto(side_by_side_server + "/Reading-Aids/A-Numbered-Section/")
        node = page.locator(".bp_sbs[data-bp-node='aids_proof_only']").first
        expect(node.locator(".bp_status_glyph").first).to_have_class(
            re.compile(r"\bbp_status_glyph_none\b"))
        chip = node.locator(".bp_code_link_status").first
        expect(chip).to_have_attribute("title", "No Lean statement")
        node.locator(".bp_code_summary_preview_wrap").first.hover()
        panel = page.locator(".bp_code_summary_preview_panel:not([hidden])")
        expect(panel).to_be_visible()
        expect(panel).to_contain_text("No Lean statement.")
        expect(panel).to_contain_text("Attached to the proof")
        expect(panel.locator(".bp_code_decl_item", has_text="aidProofOnly")).to_have_count(1)
        # the graph: neither its statement nor its proof is drawn as formalized
        page.goto(side_by_side_server + "/Dependency-Graph/", wait_until="domcontentloaded")
        graph_node = page.locator(".bp_graph_canvas svg g.node[id='bp-node-aids-005Fproof-005Fonly']")
        expect(graph_node).to_have_count(1)
        classes = graph_node.get_attribute("class") or ""
        assert "formalized" not in classes, classes
        assert (graph_node.get_attribute("aria-label") or "").endswith("No Lean declaration")
        # the summary links the declaration to the node
        page.goto(side_by_side_server + "/Blueprint-Summary/")
        hrefs = page.locator("a").evaluate_all(
            """anchors => [...new Set(anchors
                .filter((a) => a.textContent.includes('aidProofOnly') && a.href.includes('#'))
                .map((a) => a.href))]"""
        )
        assert hrefs, "the summary links the proof's declaration"
        for href in hrefs:
            page.goto(href)
            target = page.evaluate(
                """() => {
                    const el = document.getElementById(decodeURIComponent(location.hash.slice(1)));
                    const node = el && (el.closest('[data-bp-node]') || el.querySelector('[data-bp-node]'));
                    return node ? node.getAttribute('data-bp-node') : null;
                }"""
            )
            assert target == "aids_proof_only", (href, target)

    def test_summary_leads_a_proof_declaration_to_its_node(self, side_by_side_server: str, page: Page):
        """The summary's link to a declaration attached to a proof, which has no row of its own in
        this layout, lands on an element of the page it names: the node."""
        page.goto(side_by_side_server + "/Blueprint-Summary/")
        hrefs = page.locator("a").evaluate_all(
            """anchors => [...new Set(anchors
                .filter((a) => a.textContent.includes('aidOpen'))
                .map((a) => a.href))]"""
        )
        assert hrefs, "the summary links the open proof declaration"
        for href in hrefs:
            assert "#" in href, href
            page.goto(href)
            target = page.evaluate(
                """() => {
                    const el = document.getElementById(decodeURIComponent(location.hash.slice(1)));
                    const node = el && (el.closest('[data-bp-node]') || el.querySelector('[data-bp-node]'));
                    return node ? node.getAttribute('data-bp-node') : null;
                }"""
            )
            assert target == "aids_sectioned", (href, target)

    def test_graph_nodes_are_named_by_their_numbers(self, side_by_side_server: str, page: Page):
        page.set_viewport_size({"width": 1440, "height": 900})
        page.goto(side_by_side_server + "/Dependency-Graph/")
        node = page.locator(".bp_graph_canvas svg g.node[id='bp-node-aids-005Ffirst']")
        expect(node).to_have_count(1)
        label = node.get_attribute("aria-label") or ""
        # its number and name, then its state in the words of its mark
        assert re.fullmatch(r"Theorem \d+\.1 \(aids_first\): Lean proof .+", label), label
        assert node.get_attribute("role") == "button"
        texts = node.locator("text").all_text_contents()
        assert len(texts) == 1 and re.fullmatch(r"Theorem \d+\.1", texts[0]), texts
        # a node outside the document keeps its name
        assert all((n.get_attribute("aria-label") or "") for n in page.locator(".bp_graph_canvas svg g.node").all())

    def test_repository_links_name_the_built_commit(self, side_by_side_server: str, page: Page):
        page.goto(side_by_side_server + "/Reading-Aids/")
        link = page.locator("a.bp_repo_file")
        expect(link).to_have_text("README")
        href = link.get_attribute("href") or ""
        assert re.fullmatch(r"https://github\.com/[^/]+/[^/]+/blob/[0-9a-f]{40}/README\.md", href), href

    def test_front_page_names_each_revision_once_without_commit_subjects(
        self, side_by_side_server: str, page: Page
    ):
        page.goto(side_by_side_server + "/")
        metadata = page.locator(".bp_build_metadata")
        expect(metadata).to_be_visible()
        expect(metadata.locator(".bp_build_metadata_subject")).to_have_count(0)
        for code in metadata.locator("code.bp_build_metadata_commit").all_text_contents():
            parts = code.split("@")
            assert len(parts) == 1 or not parts[1].startswith(parts[0][:7]), code


def test_pages_let_the_reader_zoom(side_by_side_site_dir: Path):
    pages = list(side_by_side_site_dir.rglob("*.html"))
    assert pages
    for path in pages:
        text = path.read_text(encoding="utf-8")
        for meta in re.findall(r'<meta name="viewport"[^>]*>', text):
            assert "maximum-scale" not in meta and "user-scalable" not in meta, (path, meta)


def test_navigation_links_find_their_places(side_by_side_site_dir: Path):
    stats = (side_by_side_site_dir / "Project-Stats" / "index.html").read_text(encoding="utf-8")
    assert 'href="#bp-what-this-means"' not in stats
    assert 'href="Project-Stats/#bp-what-this-means"' in stats


def test_parts_number_chapters_across_parts(side_by_side_site_dir: Path):
    index = (side_by_side_site_dir / "index.html").read_text(encoding="utf-8")
    # the label "Part I — " is marked up so that a stylesheet can set it apart
    for numeral, title in (("I", "Relations"), ("II", "Reading")):
        label = (
            f'<span class="bp_part_label"><span class="bp_part_number">Part {numeral}</span>'
            '<span class="bp_part_separator"> — </span></span>'
        )
        assert label + title in index, title
    part_page = (side_by_side_site_dir / "Part-I" / "index.html").read_text(encoding="utf-8")
    assert "<title>Part I — Relations</title>" in part_page
    # chapters stay where they were, numbered on across the parts
    for number, title in ((5, "Group Previews"), (6, "Preview Relationships"), (9, "Reading Aids")):
        assert f'<span class="number">{number}.</span> {title}' in index, title
    assert (side_by_side_site_dir / "Preview-Relationships" / "index.html").exists()
    assert (side_by_side_site_dir / "Part-I" / "index.html").exists()
    aids = (side_by_side_site_dir / "Reading-Aids" / "index.html").read_text(encoding="utf-8")
    assert ">9.1</span>" in aids and '<span class="number">§9.1</span> A Numbered Section' in aids
    aids = (side_by_side_site_dir / "Reading-Aids" / "A-Numbered-Section" / "index.html").read_text(
        encoding="utf-8"
    )
    assert ">9.1.1</span>" in aids
    assert re.search(r">§9\.1[ \u00a0]A Numbered Section", aids), "section sign"
    assert not re.search(r"9\.1\.[ \u00a0]A Numbered Section", aids)


_AXIS_JS = r"""(sel) => {
    const centre = (b) => (b.left + b.right) / 2;
    const area = document.querySelector('main .content-wrapper > section');
    const axis = centre(area.getBoundingClientRect());
    // the centre of each line of a heading's text, without its permalink marker
    const lines = (h) => {
        const parts = [...h.childNodes].filter((n) => !(n.classList && n.classList.contains('permalink-widget')));
        const range = document.createRange();
        range.setStartBefore(parts[0]);
        range.setEndAfter(parts[parts.length - 1]);
        const rows = {};
        for (const r of range.getClientRects()) {
            if (r.width === 0) continue;
            const row = (rows[Math.round(r.bottom)] ||= { left: r.left, right: r.right });
            row.left = Math.min(row.left, r.left);
            row.right = Math.max(row.right, r.right);
        }
        return Object.values(rows).map(centre);
    };
    const h = document.querySelector(sel);
    return { axis, area: area.getBoundingClientRect().width, lines: h ? lines(h) : null };
}"""


class TestReadingAxis:
    """Every page reads about one centred axis: its title, its headings and its reading column."""

    @pytest.mark.parametrize("width", (1024, 1440))
    @pytest.mark.parametrize(
        "path", ("/Side-by-Side-Runs/", "/Part-II/", "/Project-Stats/", "/Dependency-Graph/")
    )
    def test_page_title_is_centred_on_the_content_area(
        self, side_by_side_server: str, page: Page, path: str, width: int
    ):
        page.set_viewport_size({"width": width, "height": 900})
        page.goto(side_by_side_server + path)
        page.wait_for_load_state("networkidle")
        facts = page.evaluate(_AXIS_JS, "main .content-wrapper > section > h1")
        assert facts["lines"], facts
        for line in facts["lines"]:
            assert abs(line - facts["axis"]) <= 1, (path, facts)

    def test_headings_column_and_figures_share_the_axis(self, side_by_side_server: str, page: Page):
        page.set_viewport_size({"width": 1440, "height": 900})
        page.goto(side_by_side_server + "/Reading-Aids/A-Numbered-Section/")
        page.wait_for_load_state("networkidle")
        # a figure narrower than the content area, as a site's own figure block would make it
        page.evaluate(
            """() => {
                const f = document.createElement('figure');
                f.id = 'axis-probe';
                f.style.width = '20rem';
                f.textContent = 'A figure';
                document.querySelector('main section section > h2').after(f);
            }"""
        )
        title = page.evaluate(_AXIS_JS, "main .content-wrapper > section > h1")
        axis = title["axis"]
        for line in title["lines"]:
            assert abs(line - axis) <= 1, title
        heading = page.evaluate(_AXIS_JS, "main section section > h2")
        # the long section heading wraps within the column, each line centred
        assert len(heading["lines"]) >= 2, heading
        for line in heading["lines"]:
            assert abs(line - axis) <= 1, heading
        sub = page.evaluate(_AXIS_JS, "main section section section > h3")
        for line in sub["lines"]:
            assert abs(line - axis) <= 1, sub
        boxes = page.evaluate(
            """() => [...document.querySelectorAll(
                    'main section section > :is(p, ul, blockquote, pre), #axis-probe, main section section > h2')]
                .map((e) => { const b = e.getBoundingClientRect();
                              return { tag: e.tagName, centre: (b.left + b.right) / 2, width: b.width,
                                       align: getComputedStyle(e).textAlign }; })"""
        )
        measure = page.evaluate(
            "() => document.querySelector('main section section > p').getBoundingClientRect().width"
        )
        # the reading column is narrower than the content area, so centring it is visible
        assert measure < title["area"] - 100, (measure, title)
        for box in boxes:
            assert abs(box["centre"] - axis) <= 1, (box, axis)
            if box["tag"] in ("P", "UL", "BLOCKQUOTE"):
                # text inside the column stays aligned to its start
                assert box["align"] in ("start", "left"), box
                assert box["width"] <= measure + 0.5, (box, measure)

    def test_front_page_text_reads_in_the_same_column(self, side_by_side_server: str, page: Page):
        page.set_viewport_size({"width": 1440, "height": 900})
        page.goto(side_by_side_server + "/")
        facts = page.evaluate(
            """() => {
                const area = document.querySelector('main .content-wrapper > section').getBoundingClientRect();
                return [...document.querySelectorAll('main .titlepage > p')].map((p) => {
                    const b = p.getBoundingClientRect();
                    return { centre: (b.left + b.right) / 2, width: b.width, axis: (area.left + area.right) / 2,
                             area: area.width, align: getComputedStyle(p).textAlign };
                });
            }"""
        )
        assert facts, "the front page has no text"
        for item in facts:
            assert abs(item["centre"] - item["axis"]) <= 1, item
            assert item["width"] < item["area"] - 100, item
            assert item["align"] in ("start", "left"), item

    def test_side_by_side_runs_keep_the_full_width(self, side_by_side_server: str, page: Page):
        page.set_viewport_size({"width": 1440, "height": 900})
        page.goto(side_by_side_server + "/Side-by-Side-Runs/")
        widths = page.evaluate(
            """() => { const s = document.querySelector('main .content-wrapper > section');
                       const run = s.querySelector(':scope > .bp_sbs_run');
                       return [s.getBoundingClientRect().width, run.getBoundingClientRect().width]; }"""
        )
        assert abs(widths[0] - widths[1]) <= 1, widths

    def test_stats_bands_keep_their_own_layout(self, side_by_side_server: str, page: Page):
        page.set_viewport_size({"width": 1440, "height": 900})
        page.goto(side_by_side_server + "/Project-Stats/")
        bands = page.evaluate(
            """() => [...document.querySelectorAll('section.bp_stats_band')].map((band) => {
                const style = getComputedStyle(band);
                const start = band.getBoundingClientRect().left + parseFloat(style.borderLeftWidth)
                    + parseFloat(style.paddingLeft);
                return [...band.querySelectorAll(
                    ':scope > :is(h2, p), :scope > .bp_stats_band_body > :is(h2, p)')]
                    .filter((e) => e.getBoundingClientRect().width > 0).map((e) => ({
                    tag: e.tagName, offset: e.getBoundingClientRect().left - start,
                    align: getComputedStyle(e).textAlign }));
            }).flat()"""
        )
        assert bands, "no stats bands"
        # the band text is in each band's body, beside the title
        assert any(item["tag"] == "P" for item in bands), bands
        for item in bands:
            # band titles and band text start at the band's edge, left-aligned, as on any card
            assert abs(item["offset"]) <= 1, item
            assert item["align"] in ("start", "left"), item

    @pytest.mark.parametrize(
        "path",
        ("/", "/Side-by-Side-Runs/", "/Reading-Aids/A-Numbered-Section/", "/Part-II/", "/Project-Stats/"),
    )
    def test_no_width_scrolls_the_page_sideways(self, side_by_side_server: str, page: Page, path: str):
        # phone widths, the widths where the table of contents leaves a narrow content area, and a sweep
        widths = sorted({360, 390, 560, 700, 701, 720, 800, 900, 1000, 1024, 1440, 1920, *range(701, 1001, 33)})
        for width in widths:
            page.set_viewport_size({"width": width, "height": 900})
            page.goto(side_by_side_server + path)
            page.wait_for_load_state("networkidle")
            sizes = page.evaluate(
                "() => [document.documentElement.scrollWidth, document.documentElement.clientWidth]"
            )
            assert sizes[0] <= sizes[1], (path, width, sizes)
            # each heading's permalink marker stays on the screen
            boxes = page.evaluate(
                "() => [...document.querySelectorAll('main .permalink-widget.inline > a')]"
                ".map((a) => { const b = a.getBoundingClientRect(); return [b.left, b.right]; })"
            )
            assert all(left >= -0.5 and right <= sizes[1] + 0.5 for left, right in boxes), (path, width, boxes)
            facts = page.evaluate(_AXIS_JS, "main .content-wrapper > section > h1, main .titlepage > h1")
            for line in facts["lines"] or []:
                assert abs(line - facts["axis"]) <= 1, (path, width, facts)

    @pytest.mark.parametrize("width", (390, 720))
    def test_permalink_marker_costs_a_title_no_line(self, side_by_side_server: str, page: Page, width: int):
        page.set_viewport_size({"width": width, "height": 900})
        page.goto(side_by_side_server + "/Reading-Aids/A-Numbered-Section/")
        page.wait_for_load_state("networkidle")
        selector = "main .content-wrapper > section > h1"
        with_marker = page.evaluate(_AXIS_JS, selector)
        padding = page.evaluate(f"() => getComputedStyle(document.querySelector('{selector}')).paddingInlineStart")
        assert padding == "0px", padding
        page.evaluate(f"() => document.querySelector('{selector} > .permalink-widget').remove()")
        without_marker = page.evaluate(_AXIS_JS, selector)
        assert len(with_marker["lines"]) == len(without_marker["lines"]), (with_marker, without_marker)

    def test_permalink_marker_shows_with_the_keyboard_focus(self, side_by_side_server: str, page: Page):
        for width in (390, 1440):
            page.set_viewport_size({"width": width, "height": 900})
            page.goto(side_by_side_server + "/Reading-Aids/A-Numbered-Section/")
            marker = page.locator("main .content-wrapper > section > h1 > .permalink-widget.inline")
            assert marker.evaluate("(e) => getComputedStyle(e).opacity") == "0"
            marker.locator("a").focus()
            assert marker.evaluate("(e) => getComputedStyle(e).opacity") == "1"
            box = marker.locator("a").bounding_box()
            assert box is not None and box["x"] >= 0 and box["x"] + box["width"] <= width, (width, box)

    def test_block_quotes_and_low_headings_keep_to_the_column(self, side_by_side_server: str, page: Page):
        page.set_viewport_size({"width": 1440, "height": 900})
        page.goto(side_by_side_server + "/Reading-Aids/A-Numbered-Section/")
        facts = page.evaluate(
            """() => {
                const area = document.querySelector('main .content-wrapper > section').getBoundingClientRect();
                const axis = (area.left + area.right) / 2;
                const section = document.querySelector('main section section');
                const para = section.querySelector(':scope > p').getBoundingClientRect();
                const quote = section.querySelector(':scope > blockquote');
                const q = quote.getBoundingClientRect();
                const text = quote.firstElementChild.getBoundingClientRect();
                const low = document.createElement('h5');
                low.textContent = 'A fifth-level heading';
                section.querySelector(':scope > p').after(low);
                const l = low.getBoundingClientRect();
                return { axis, paraLeft: para.left, paraWidth: para.width,
                         quoteCentre: (q.left + q.right) / 2, quoteWidth: q.width,
                         indent: [text.left - q.left, q.right - text.right],
                         lowAlign: getComputedStyle(low).textAlign, lowLeft: l.left, lowWidth: l.width };
            }"""
        )
        # a block quote is the column, its text indented from both edges
        assert abs(facts["quoteCentre"] - facts["axis"]) <= 1, facts
        assert abs(facts["quoteWidth"] - facts["paraWidth"]) <= 1, facts
        assert all(abs(side - 40) <= 1 for side in facts["indent"]), facts
        # a fifth-level heading starts at the column's edge, within the measure
        assert facts["lowAlign"] in ("start", "left"), facts
        assert abs(facts["lowLeft"] - facts["paraLeft"]) <= 1, facts
        assert facts["lowWidth"] <= facts["paraWidth"] + 0.5, facts

    @pytest.mark.parametrize("length", ("short", "medium", "long"))
    def test_code_blocks_grow_about_the_axis(self, side_by_side_server: str, page: Page, length: str):
        page.set_viewport_size({"width": 1440, "height": 900})
        page.goto(side_by_side_server + "/Reading-Aids/A-Numbered-Section/")
        line = {"short": "x := 1", "medium": "theorem t " + "abc " * 18, "long": "theorem t " + "abcdef " * 60}[length]
        facts = page.evaluate(
            """(line) => {
                const area = document.querySelector('main .content-wrapper > section').getBoundingClientRect();
                const block = document.querySelector('main section section > pre');
                block.textContent = line;
                const b = block.getBoundingClientRect();
                const column = document.querySelector('main section section > p').getBoundingClientRect();
                return { offset: (b.left + b.right) / 2 - (area.left + area.right) / 2, width: b.width,
                         column: column.width, area: area.width,
                         scrolls: block.scrollWidth > block.clientWidth };
            }""",
            line,
        )
        assert abs(facts["offset"]) <= 1, facts
        if length == "short":
            assert abs(facts["width"] - facts["column"]) <= 1 and not facts["scrolls"], facts
        elif length == "medium":
            assert facts["column"] + 10 < facts["width"] < facts["area"] - 10 and not facts["scrolls"], facts
        else:
            assert abs(facts["width"] - facts["area"]) <= 1 and facts["scrolls"], facts

    def test_lists_of_sections_search_and_notices(self, side_by_side_server: str, page: Page):
        page.set_viewport_size({"width": 1440, "height": 900})
        page.goto(side_by_side_server + "/")
        toc = page.evaluate(
            """() => {
                const area = document.querySelector('main .content-wrapper > section').getBoundingClientRect();
                const list = document.querySelector('main section > ol.section-toc');
                const b = list.getBoundingClientRect();
                return { offset: (b.left + b.right) / 2 - (area.left + area.right) / 2, width: b.width,
                         area: area.width, align: getComputedStyle(list.querySelector('li')).textAlign };
            }"""
        )
        # the list of sections is centred as a block, its entries aligned to their start
        assert abs(toc["offset"]) <= 1 and toc["width"] < toc["area"] / 2, toc
        assert toc["align"] in ("start", "left"), toc
        page.goto(side_by_side_server + "/search/")
        assert page.locator("main section.search-page > h1").evaluate("(e) => getComputedStyle(e).textAlign") == "center"
        # a licence notice keeps its own layout
        page.goto(side_by_side_server + "/Reading-Aids/A-Numbered-Section/")
        aligns = page.evaluate(
            """() => {
                document.querySelector('main section section').insertAdjacentHTML('beforeend',
                    '<section class="license-info"><h3>A dependency</h3>'
                    + '<section><h4>Its notice</h4><p>The text of the licence.</p></section></section>');
                const h = document.querySelector('.license-info section > h4');
                return [getComputedStyle(h).textAlign, getComputedStyle(h).marginLeft];
            }"""
        )
        assert aligns == ["start", "0px"], aligns


# The page of the fixture with Lean code in its running text: a block and inline code.
PROSE_LEAN_PAGE = "/Reading-Aids/Lean-in-the-Text/"

# The places of the running text where a Lean block is a block of the text.
_PROSE_PLACES = (
    "main section:not([class]), main .titlepage, main section:not([class]) > :is(ul, ol) > li, "
    "main section:not([class]) > blockquote, main section:not([class]) > dl > dd, div.paragraph, "
    ".bp_content"
)

# Lean blocks of the running text, as opposed to those of the Blueprint's own components.
_PROSE_BLOCK_JS = """() => [...document.querySelectorAll('code.hl.lean.block')].filter((b) =>
    b.parentElement.matches('""" + _PROSE_PLACES + """'))"""

# Lean blocks of the Blueprint's own components: the Lean column, code panels, the code of the
# Comparator and statistics pages.
_COMPONENT_BLOCKS = (
    ".bp_sbs_formal code.hl.lean.block, details.bp_code_block code.hl.lean.block, "
    ".bp_comparator_code code.hl.lean.block, .bp_stats_statement_code code.hl.lean.block"
)

# Each visible token of the Lean code that `selector` finds (in `root`, a function giving the
# elements), with its contrast against the colour behind it.
_TOKEN_CONTRAST_JS = """(roots) => {
  // `rgb(…)`/`rgba(…)` in 0–255, or `color(srgb …)` in 0–1 (what `color-mix` computes to)
  const parse = (c) => {
    const p = c.match(/[\\d.]+/g).map(Number);
    const k = c.startsWith('color(') ? 255 : 1;
    return { r: p[0] * k, g: p[1] * k, b: p[2] * k, a: p.length > 3 ? p[3] : 1 };
  };
  const lum = (c) => { const f = (v) => { v /= 255; return v <= 0.03928 ? v / 12.92 : Math.pow((v + 0.055) / 1.055, 2.4); }; return 0.2126 * f(c.r) + 0.7152 * f(c.g) + 0.0722 * f(c.b); };
  // the colour behind an element: its ancestors' backgrounds laid over the canvas (white)
  const behind = (el) => {
    const layers = [];
    for (let e = el; e; e = e.parentElement) {
      const c = parse(getComputedStyle(e).backgroundColor);
      if (c.a > 0) layers.push(c);
      if (c.a >= 1) break;
    }
    let out = { r: 255, g: 255, b: 255, a: 1 };
    for (const c of layers.reverse()) {
      out = { r: c.r * c.a + out.r * (1 - c.a), g: c.g * c.a + out.g * (1 - c.a),
              b: c.b * c.a + out.b * (1 - c.a), a: 1 };
    }
    return out;
  };
  const out = {};
  for (const [name, selector] of Object.entries(roots)) {
    const elements = selector === 'prose'
      ? (""" + _PROSE_BLOCK_JS + """)()
      : [...document.querySelectorAll(selector)];
    out[name] = elements.flatMap((root) => [...root.querySelectorAll('.token')])
      .filter((el) => el.textContent.trim() && el.getClientRects().length)
      .map((el) => {
        const [x, y] = [lum(parse(getComputedStyle(el).color)), lum(behind(el))].sort((p, q) => q - p);
        return [el.className, el.textContent.slice(0, 20), (x + 0.05) / (y + 0.05)];
      });
  }
  return { dark: lum(behind(document.body)) < 0.05, out };
}"""


class TestLeanInTheText:
    """Lean code of the running text: highlighted, framed, linked and with hovers like the Lean column."""

    @pytest.mark.parametrize("scheme", ("light", "dark"))
    def test_code_tokens_are_readable(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page, scheme: str
    ):
        page.emulate_media(color_scheme=scheme)
        for path, roots in (
            (side_by_side_page_path(side_by_side_site_dir), {"column": ".bp_sbs_formal .hl.lean"}),
            (PROSE_LEAN_PAGE, {"block": "prose", "inline": "code.hl.lean.inline"}),
        ):
            page.goto(side_by_side_server + path)
            page.evaluate("() => document.querySelectorAll('details').forEach(d => d.open = true)")
            # the tokens' colours ease in; measure them once they have settled
            page.wait_for_function(
                "document.getAnimations().every((a) => a.playState !== 'running')", timeout=5000
            )
            result = page.evaluate(_TOKEN_CONTRAST_JS, roots)
            assert result["dark"] == (scheme == "dark"), (path, scheme)
            for name, tokens in result["out"].items():
                assert tokens, (path, name)
                failing = [t for t in tokens if t[2] < 4.5]
                assert not failing, (path, scheme, name, failing)

    @pytest.mark.parametrize("scheme", ("light", "dark"))
    def test_prose_tokens_take_the_palette(self, side_by_side_server: str, page: Page, scheme: str):
        page.emulate_media(color_scheme=scheme)
        page.goto(side_by_side_server + PROSE_LEAN_PAGE)
        page.wait_for_function(
            "document.getAnimations().every((a) => a.playState !== 'running')", timeout=5000
        )
        colours = page.evaluate(
            """() => {
              const probe = document.createElement('span');
              document.body.appendChild(probe);
              const palette = (name, fallback) => {
                probe.style.color = `var(${name}, ${fallback})`;
                return getComputedStyle(probe).color;
              };
              const block = (""" + _PROSE_BLOCK_JS + """)()[0];
              const first = (sel) => { const e = block.querySelector(sel); return e && getComputedStyle(e).color; };
              const inline = document.querySelector('code.hl.lean.inline .const.token');
              return {
                const: [first('.const.token'), palette('--bp-code-const', '#8a5a00')],
                keyword: [first('.keyword.token'), palette('--bp-code-keyword', '#0b52b5')],
                comment: [first('.comment.token, .doc-comment.token'), palette('--bp-code-comment', '#5f6b78')],
                inlineConst: [inline && getComputedStyle(inline).color, palette('--bp-code-const', '#8a5a00')],
              };
            }"""
        )
        for kind, (actual, expected) in colours.items():
            assert actual == expected, (scheme, kind, actual, expected)

    def test_prose_block_is_framed_on_the_reading_column(self, side_by_side_server: str, page: Page):
        for width in (1440, 360):
            page.set_viewport_size({"width": width, "height": 900})
            page.goto(side_by_side_server + PROSE_LEAN_PAGE)
            facts = page.evaluate(
                """() => {
                  const b = (""" + _PROSE_BLOCK_JS + """)()[0];
                  const p = b.parentElement.querySelector(':scope > p');
                  const cs = getComputedStyle(b);
                  const box = b.getBoundingClientRect(), text = p.getBoundingClientRect();
                  const section = b.parentElement.getBoundingClientRect();
                  return { border: cs.borderTopWidth, overflow: cs.overflowX, padding: cs.paddingLeft,
                           left: box.left, width: box.width, right: box.right,
                           textLeft: text.left, textWidth: text.width, sectionRight: section.right,
                           scrolls: b.scrollWidth > b.clientWidth,
                           page: [document.documentElement.scrollWidth, document.documentElement.clientWidth] };
                }"""
            )
            assert facts["border"] == "1px" and facts["overflow"] == "auto", facts
            assert float(facts["padding"][:-2]) > 4, facts
            # it sits on the paragraphs' axis, is at least as wide as they are, and stays in the
            # content area: a line longer than that scrolls inside the block, not the page
            centre = (facts["left"] + facts["right"]) / 2
            assert abs(centre - (facts["textLeft"] + facts["textWidth"] / 2)) <= 1, (width, facts)
            assert facts["width"] >= facts["textWidth"] - 1, (width, facts)
            assert facts["right"] <= facts["sectionRight"] + 1, (width, facts)
            assert facts["page"][0] <= facts["page"][1], (width, facts)
            if width == 360:
                assert facts["scrolls"], facts

    def test_prose_lean_block_shares_the_plain_code_block_geometry(
        self, side_by_side_server: str, page: Page
    ):
        # a Lean block of the text and a plain code block of the prose: both on the page's axis,
        # both at least as wide as the reading column, both within the content area
        js = """(sel) => {
            const b = document.querySelector(sel);
            const area = document.querySelector('main .content-wrapper > section').getBoundingClientRect();
            const p = b.parentElement.querySelector(':scope > p').getBoundingClientRect();
            const box = b.getBoundingClientRect(), cs = getComputedStyle(b);
            return { offset: (box.left + box.right) / 2 - (area.left + area.right) / 2,
                     wide: box.width >= p.width - 1, inside: box.right <= area.right + 1,
                     minWidth: cs.minWidth, maxWidth: cs.maxWidth };
        }"""
        for width in (1920, 1440, 1024, 390):
            page.set_viewport_size({"width": width, "height": 900})
            page.goto(side_by_side_server + "/Reading-Aids/A-Numbered-Section/")
            plain = page.evaluate(js, "main section:not([class]) > pre")
            page.goto(side_by_side_server + PROSE_LEAN_PAGE)
            lean = page.evaluate(js, "main section:not([class]) > code.hl.lean.block")
            for facts in (plain, lean):
                assert abs(facts["offset"]) <= 1 and facts["wide"] and facts["inside"], (width, plain, lean)
            assert (plain["minWidth"], plain["maxWidth"]) == (lean["minWidth"], lean["maxWidth"]), (
                width, plain, lean)

    def test_blueprint_components_keep_their_own_code_layout(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        seen = 0
        for path in (side_by_side_page_path(side_by_side_site_dir), "/Code-Panels/", "/Project-Stats/"):
            page.goto(side_by_side_server + path)
            page.evaluate("() => document.querySelectorAll('details').forEach(d => d.open = true)")
            framed = page.evaluate(
                """(sel) => [...document.querySelectorAll(sel)].map((b) => {
                  const cs = getComputedStyle(b);
                  return [b.parentElement.className, cs.borderTopStyle, cs.borderTopWidth, cs.minWidth];
                })""",
                _COMPONENT_BLOCKS,
            )
            seen += len(framed)
            # none of them gets the frame of a Lean block of the text
            assert all(f[1] == "none" or f[2] == "0px" for f in framed), (path, framed)
            assert not page.evaluate(
                "(sel) => [...document.querySelectorAll(sel)].some((b) => b.parentElement.matches(" +
                repr(_PROSE_PLACES) + "))",
                _COMPONENT_BLOCKS,
            ), path
        assert seen, "no component code on these pages"

    @pytest.mark.parametrize("scheme", ("light", "dark"))
    def test_lean_messages_keep_their_colours(self, side_by_side_server: str, page: Page, scheme: str):
        page.emulate_media(color_scheme=scheme)
        page.goto(side_by_side_server + PROSE_LEAN_PAGE)
        page.wait_for_function(
            "document.getAnimations().every((a) => a.playState !== 'running')", timeout=5000
        )
        result = page.evaluate(
            """() => {
              const probe = document.createElement('span');
              document.body.appendChild(probe);
              probe.style.color = 'var(--verso-message-error-color, #cc0000)';
              const error = getComputedStyle(probe).color;
              const tokens = [...document.querySelectorAll('.error .verso-message .token')]
                .filter((t) => t.textContent.trim());
              return { error, tokens: tokens.map((t) => [t.textContent, getComputedStyle(t).color]) };
            }"""
        )
        assert result["tokens"], result
        wrong = [t for t in result["tokens"] if t[1] != result["error"]]
        assert not wrong, (scheme, result["error"], wrong)

    def test_hovering_a_prose_token_shows_its_tooltip(self, side_by_side_server: str, page: Page):
        errors = record_runtime_errors(page)
        page.goto(side_by_side_server + PROSE_LEAN_PAGE)
        page.wait_for_load_state("networkidle")
        _hover_prose_constant(page)
        assert_no_runtime_errors(errors)

    def test_hovering_a_prose_token_shows_its_tooltip_from_a_file(
        self, side_by_side_site_dir: Path, page: Page
    ):
        assert (side_by_side_site_dir / "-verso-docs.js").is_file()
        page.goto((side_by_side_site_dir / PROSE_LEAN_PAGE.strip("/") / "index.html").as_uri())
        page.wait_for_load_state("load")
        _hover_prose_constant(page)

    def test_project_constant_links_to_its_lean_row(
        self, side_by_side_server: str, side_by_side_site_dir: Path, page: Page
    ):
        page.goto(side_by_side_server + PROSE_LEAN_PAGE)
        link = page.locator("code.hl.lean.block a:has(.const.token[data-binding$='.aidBase'])").first
        expect(link).to_have_count(1)
        href = link.get_attribute("href") or ""
        page_path, _, anchor = href.partition("#")
        assert anchor, href
        target = side_by_side_site_dir / page_path / "index.html"
        assert f'id="{anchor}"' in target.read_text(encoding="utf-8"), href
        link.click()
        page.wait_for_url(re.compile(re.escape("#" + anchor) + "$"))
        expect(page.locator(f'[id="{anchor}"]')).to_be_attached()
        # a declaration of Lean itself has no place on the site
        expect(page.locator("code.hl.lean.block a:has(.const.token[data-binding='const-Nat.le_trans'])")).to_have_count(0)

    def test_project_constant_links_to_its_source_at_the_commit(self, side_by_side_server: str, page: Page):
        source = PACKAGE_ROOT / "tests/test_blueprints/preview_runtime_showcase/PreviewRuntimeShowcase/Chapters/ReadingAids.lean"
        rel = source.relative_to(PACKAGE_ROOT).as_posix()
        page.goto(side_by_side_server + PROSE_LEAN_PAGE)
        link = page.locator("code.hl.lean.block a:has(.const.token[data-binding$='.aidSlack'])").first
        origin = subprocess.run(["git", "remote", "get-url", "origin"], cwd=PACKAGE_ROOT,
                                capture_output=True, text=True).stdout.strip()
        if "github.com" not in origin:
            pytest.skip("the checkout has no GitHub origin, so its files have no address")
        head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=PACKAGE_ROOT,
                              capture_output=True, text=True, check=True).stdout.strip()
        clean = subprocess.run(["git", "diff", "--quiet", "HEAD", "--", str(source)], cwd=PACKAGE_ROOT).returncode == 0
        if not clean:
            # a file that differs from the commit has no address at it
            expect(link).to_have_count(0)
            return
        href = link.get_attribute("href") or ""
        m = re.fullmatch(r"https://github\.com/[^/]+/[^/]+/blob/([0-9a-f]{40})/(.+)#L(\d+)(?:-L(\d+))?", href)
        assert m, href
        # the commit the site was built from, and the file there
        assert m.group(1) == head, (href, head)
        assert m.group(2) == rel, href
        lines = source.read_text(encoding="utf-8").splitlines()
        start, stop = int(m.group(3)), int(m.group(4) or m.group(3))
        assert any("def aidSlack" in line for line in lines[start - 1 : stop]), (href, lines[start - 1 : stop])


def _hover_prose_constant(page: Page) -> None:
    # the constant in the theorem's statement, outside its proof's tactics
    token = page.locator("code.hl.lean.block .const.token[data-verso-hover][data-binding$='.aidSlack']").first
    token.scroll_into_view_if_needed()
    token.hover()
    box = page.locator(".tippy-box[data-theme~='lean']").first
    expect(box).to_be_visible()
    expect(box).to_contain_text("aidSlack")
    expect(box).to_contain_text("A bound that no statement of the Blueprint names")
    expect(box).not_to_contain_text("Failed to load")

