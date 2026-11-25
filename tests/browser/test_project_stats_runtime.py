"""Browser checks for the Project Stats page that generators add to every site.

The page is reached from the table of contents, draws progress statuses with the shared status
tokens (each status with its own pattern, so colour is never the only signal), keeps its text
readable in the light and the dark theme, and fits a phone-width window without scrolling
sideways.
"""

import re

import pytest
from playwright.sync_api import Page

from support import assert_no_runtime_errors, record_runtime_errors
from test_dark_theme_runtime import COLOR_HELPERS, MIN_CONTRAST

STATS_PATH = "/Project-Stats/"

# Text the page shows, by selector: each must be readable on the background it is drawn on.
TEXT_SELECTORS = [
    ".bp_stats_band_title",
    ".bp_stats_lead",
    ".bp_stats_chip",
    ".bp_stats_fact_label",
    ".bp_stats_caption",
    ".bp_stats_legend_item",
    ".bp_stats_tile_value",
    ".bp_stats_tile_label",
    ".bp_stats_tile_detail",
    ".bp_stats_build_line",
    ".bp_stats_ledger th",
    ".bp_stats_ledger td",
    ".bp_stats_summary_link a",
]

TEXT_REPORTS = """
(selectors) => {
""" + COLOR_HELPERS + """
  const out = [];
  for (const sel of selectors) {
    for (const el of document.querySelectorAll(sel)) {
      if (!el.textContent.trim()) continue;
      out.push(Object.assign({ sel, text: el.textContent.trim().slice(0, 40) }, report(el)));
    }
  }
  return out;
}
"""

# Per bar segment: its status, computed fill and pattern, and the colour of its status token.
SEGMENT_REPORTS = """
() => {
""" + COLOR_HELPERS + """
  const probe = document.createElement('span');
  document.body.appendChild(probe);
  const tokenColor = (name) => {
    probe.style.color = 'var(' + name + ')';
    return parse(getComputedStyle(probe).color);
  };
  const tokens = {
    'fully-proved': '--bp-color-status-formalized-with-ancestors',
    'open-ancestors': '--bp-color-status-formalized',
    'incomplete': '--bp-color-status-incomplete',
    'ready': '--bp-color-status-ready',
    'not-ready': '--bp-color-status-not-ready',
  };
  const out = [];
  for (const el of document.querySelectorAll('.bp_stats_seg, .bp_stats_swatch')) {
    const status = [...el.classList].find((c) => c.startsWith('bp_stats_status_')).slice('bp_stats_status_'.length);
    const style = getComputedStyle(el);
    out.push({
      status, swatch: el.classList.contains('bp_stats_swatch'),
      fill: parse(style.backgroundColor), token: tokenColor(tokens[status]),
      pattern: style.backgroundImage, width: el.getBoundingClientRect().width,
    });
  }
  probe.remove();
  return out;
}
"""


def same_rgb(a: dict, b: dict) -> bool:
    return all(abs(a[k] - b[k]) < 1 for k in ("r", "g", "b"))


def open_stats(page: Page, server: str, scheme: str) -> None:
    page.emulate_media(color_scheme=scheme)
    page.goto(server + STATS_PATH, wait_until="domcontentloaded", timeout=60000)
    page.wait_for_selector(".bp_project_stats", timeout=60000)


class TestProjectStatsRuntime:
    def test_reached_from_the_table_of_contents(self, server: str, page: Page):
        errors = record_runtime_errors(page)
        page.goto(server + "/", wait_until="domcontentloaded", timeout=60000)
        link = page.locator("#toc a", has_text="Project Stats").first
        assert link.count() == 1
        link.click()
        page.wait_for_selector(".bp_project_stats", timeout=60000)
        assert page.url.rstrip("/").endswith("Project-Stats") or "Project-Stats" in page.url
        for band in ("bp_stats_identity", "bp_stats_progress", "bp_stats_size", "bp_stats_build",
                     "bp_stats_trust"):
            assert page.locator("." + band).count() == 1, band
        # The showcase has no Comparator challenge: the hint replaces the headline card.
        assert page.locator(".bp_stats_headline_hint").count() == 1
        assert page.locator(".bp_stats_band.bp_stats_headline").count() == 0
        assert_no_runtime_errors(errors)

    @pytest.mark.parametrize("scheme", ["light", "dark"])
    def test_text_is_readable(self, server: str, page: Page, scheme: str):
        open_stats(page, server, scheme)
        reports = page.evaluate(TEXT_REPORTS, TEXT_SELECTORS)
        assert len(reports) >= len(TEXT_SELECTORS), reports
        body_lum = page.evaluate("() => {" + COLOR_HELPERS + "return report(document.body).bgLum; }")
        assert (body_lum > 0.8) if scheme == "light" else (body_lum < 0.05), body_lum
        failing = [r for r in reports if r["ratio"] < MIN_CONTRAST]
        assert not failing, failing

    @pytest.mark.parametrize("scheme", ["light", "dark"])
    def test_status_segments_use_the_tokens_and_patterns(self, server: str, page: Page, scheme: str):
        open_stats(page, server, scheme)
        reports = page.evaluate(SEGMENT_REPORTS)
        assert [r for r in reports if r["swatch"]], reports
        assert [r for r in reports if not r["swatch"]], reports
        for r in reports:
            assert same_rgb(r["fill"], r["token"]), r
            # Every status but "fully proved" has a pattern, so colour is not the only signal.
            assert (r["pattern"] == "none") == (r["status"] == "fully-proved"), r
            if not r["swatch"]:
                assert r["width"] > 0, r

    def test_fits_a_phone_width(self, server: str, page: Page):
        page.set_viewport_size({"width": 390, "height": 844})
        open_stats(page, server, "light")
        overflow = page.evaluate(
            "() => document.scrollingElement.scrollWidth - document.scrollingElement.clientWidth"
        )
        assert overflow <= 0, overflow
        wide = page.evaluate(
            """() => [...document.querySelectorAll('.bp_project_stats *')]
                 .filter((el) => el.getBoundingClientRect().right > window.innerWidth + 1)
                 .map((el) => el.className || el.tagName).slice(0, 5)"""
        )
        assert not wide, wide


# Every chip and pill of the page's bands, with its list item, its box and its link.
CHIP_REPORTS = """
() => [...document.querySelectorAll(
    '.bp_stats_chips > li, .bp_stats_axiom_list > li')].map((li) => {
  const chip = li.firstElementChild;
  const box = chip.getBoundingClientRect();
  const s = getComputedStyle(chip), ls = getComputedStyle(li);
  const list = li.parentElement;
  return {
    list: [...document.querySelectorAll('.bp_stats_chips, .bp_stats_axiom_list')].indexOf(list),
    listWidth: list.getBoundingClientRect().width,
    holderWidth: list.parentElement.getBoundingClientRect().width,
    top: box.top, bottom: box.bottom, right: box.right, width: box.width,
    listLeft: list.getBoundingClientRect().left,
    fill: list.classList.contains('bp_stats_chips'),
    margins: [s.marginTop, s.marginBottom, ls.marginTop, ls.marginBottom],
    tag: chip.tagName, cls: chip.className, href: chip.getAttribute('href'),
    rel: chip.getAttribute('rel'), toolchain: chip.dataset.bpToolchain || null,
    font: s.fontFamily, text: chip.textContent.trim(),
  };
})
"""

RELEASE = re.compile(r"^(leanprover/lean4:)?(v\d+\.\d+\.\d+(-rc\d+)?)$")

HREF_FORMS = {
    "bp_stats_chip_package": re.compile(r"^https://github\.com/[\w.-]+/[\w.-]+/tree/[0-9a-f]{40}$"),
    "bp_stats_chip_license": re.compile(r"^https://github\.com/[\w.-]+/[\w.-]+/blob/[0-9a-f]{40}/\S+$"),
    "bp_stats_chip_toolchain": re.compile(
        r"^https://github\.com/leanprover/lean4/releases/tag/v\d+\.\d+\.\d+(-rc\d+)?$"),
    "bp_stats_axiom": re.compile(r"^https://lean-lang\.org/doc/reference/latest/\S+#\S+$"),
}


def check_chips(chips: list[dict]) -> None:
    """Chips of one row share one top and one bottom, have no margins, and fill a list as wide as
    what holds it before they wrap; a chip with an address is a link of the expected form that
    leaves the site safely, and a chip without one is not a link."""
    assert chips
    for c in chips:
        assert all(m == "0px" for m in c["margins"]), c
    lists: dict[int, list[dict]] = {}
    for c in chips:
        lists.setdefault(c["list"], []).append(c)
    for row_chips in lists.values():
        first = row_chips[0]
        # the identity's lists take the width of what holds them: no reading measure on chips
        if first["fill"]:
            assert first["listWidth"] >= first["holderWidth"] - 1, first
        rows: list[list[dict]] = []
        for c in row_chips:
            if rows and abs(rows[-1][0]["top"] - c["top"]) < 4:
                rows[-1].append(c)
            else:
                rows.append([c])
        for row in rows:
            assert max(c["top"] for c in row) - min(c["top"] for c in row) < 0.5, row
            assert max(c["bottom"] for c in row) - min(c["bottom"] for c in row) < 0.5, row
        # a chip moves to the next row only when it would not fit on the row before it
        for before, after in zip(rows, rows[1:]):
            used = max(c["right"] for c in before) - first["listLeft"]
            assert used + after[0]["width"] > first["listWidth"] - 1, (before, after)
    for c in chips:
        kind = next((k for k in HREF_FORMS if k in c["cls"].split()), None)
        if c["tag"] == "A":
            assert kind, c
            assert HREF_FORMS[kind].match(c["href"]), c
            assert c["rel"] == "noopener", c
        if "bp_stats_chip_missing" in c["cls"]:
            assert c["tag"] != "A", c
        if kind == "bp_stats_chip_toolchain":
            assert (c["tag"] == "A") == bool(RELEASE.match(c["toolchain"])), c


def check_one_face(page: Page) -> None:
    """Captions, labels, chips and pills are set in one face."""
    faces = page.evaluate(
        """() => [...document.querySelectorAll('.bp_stats_caption, .bp_stats_fact_label, '
                 + '.bp_stats_chip, .bp_stats_axiom, .bp_stats_verdict, .bp_stats_axioms_note')]
             .map((el) => getComputedStyle(el).fontFamily)"""
    )
    assert faces and len(set(faces)) == 1, set(faces)


class TestProjectStatsCraft:
    @pytest.mark.parametrize("width", [1440, 390])
    def test_chips_align_wrap_late_and_link_as_their_data_allows(self, server: str, page: Page, width: int):
        page.set_viewport_size({"width": width, "height": 900})
        open_stats(page, server, "light")
        check_chips(page.evaluate(CHIP_REPORTS))

    def test_captions_labels_and_chips_share_one_face(self, server: str, page: Page):
        open_stats(page, server, "light")
        check_one_face(page)

    def test_landing_on_the_page_title_does_not_mark_it(self, server: str, page: Page):
        page.goto(server + "/", wait_until="domcontentloaded", timeout=60000)
        href = page.locator("#toc a", has_text="Project Stats").first.get_attribute("href")
        assert "#" in href, href
        page.locator("#toc a", has_text="Project Stats").first.click()
        page.wait_for_selector(".bp_project_stats", timeout=60000)
        page.wait_for_timeout(300)
        marked = page.evaluate("() => [...document.querySelectorAll('.bp_decl_target')].map((e) => e.tagName)")
        assert marked == [], marked
        background = page.evaluate("getComputedStyle(document.querySelector('main h1')).backgroundColor")
        assert background in ("rgba(0, 0, 0, 0)", "transparent"), background
