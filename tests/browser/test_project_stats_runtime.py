"""Browser checks for the Project Stats page that generators add to every site.

The page is reached from the table of contents, draws progress statuses with the shared status
tokens (each status with its own pattern, so colour is never the only signal), keeps its text
readable in the light and the dark theme, and fits a phone-width window without scrolling
sideways.
"""

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
