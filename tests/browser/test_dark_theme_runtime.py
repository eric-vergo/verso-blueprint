"""Browser checks for the dark theme: computed colours and text contrast.

The dark theme follows `html[data-theme="dark"]` and, without an explicit
choice, the operating system preference. These checks read computed colours
in a real browser and hold body text and code tokens to the WCAG AA contrast
ratio for normal text (4.5:1) against the background they are drawn on.
"""

from playwright.sync_api import Page

from support import assert_no_runtime_errors, record_runtime_errors

MIN_CONTRAST = 4.5

# Shared colour helpers, evaluated in the page.
COLOR_HELPERS = """
const parse = (c) => {
  const m = c.match(/rgba?\\(([^)]+)\\)/);
  if (!m) return null;
  const p = m[1].split(/[ ,\\/]+/).filter(Boolean).map(Number);
  return { r: p[0], g: p[1], b: p[2], a: p.length > 3 ? p[3] : 1 };
};
const lum = (c) => {
  const f = (v) => { v /= 255; return v <= 0.03928 ? v / 12.92 : Math.pow((v + 0.055) / 1.055, 2.4); };
  return 0.2126 * f(c.r) + 0.7152 * f(c.g) + 0.0722 * f(c.b);
};
const contrast = (a, b) => {
  const [x, y] = [lum(a), lum(b)].sort((p, q) => q - p);
  return (x + 0.05) / (y + 0.05);
};
// The colour an element's text is drawn on: the nearest opaque-enough background.
const backgroundOf = (el) => {
  for (let e = el; e; e = e.parentElement) {
    const c = parse(getComputedStyle(e).backgroundColor);
    if (c && c.a >= 0.5) return c;
  }
  // Nothing painted: the canvas of a light page.
  return { r: 255, g: 255, b: 255, a: 1 };
};
// Semi-transparent text is seen blended onto its background.
const blend = (fg, bg) => ({
  r: fg.r * fg.a + bg.r * (1 - fg.a),
  g: fg.g * fg.a + bg.g * (1 - fg.a),
  b: fg.b * fg.a + bg.b * (1 - fg.a),
  a: 1,
});
const report = (el) => {
  const bg = backgroundOf(el);
  const fg = blend(parse(getComputedStyle(el).color), bg);
  return { fg, bg, ratio: contrast(fg, bg), fgLum: lum(fg), bgLum: lum(bg) };
};
"""


def measure(page: Page, selector: str) -> dict:
    return page.evaluate(
        "(sel) => {" + COLOR_HELPERS + "const el = document.querySelector(sel); return el ? report(el) : null; }",
        selector,
    )


def token_reports(page: Page) -> list[dict]:
    """One report per distinct token class of the highlighted Lean code on the page."""
    return page.evaluate(
        "() => {"
        + COLOR_HELPERS
        + """
        const seen = new Map();
        for (const el of document.querySelectorAll('.hl.lean .token')) {
          if (!el.textContent.trim()) continue;
          const kind = [...el.classList].filter((c) => c !== 'token').sort().join('.');
          if (seen.has(kind)) continue;
          seen.set(kind, Object.assign({ kind, text: el.textContent.slice(0, 24) }, report(el)));
        }
        return [...seen.values()];
        }"""
    )


class TestDarkThemeRuntime:
    def test_follows_os_preference(self, server: str, page: Page):
        errors = record_runtime_errors(page)
        page.emulate_media(color_scheme="dark")
        page.goto(server + "/Code-Panels/")
        body = measure(page, "body")
        assert body["bgLum"] < 0.05, body
        assert body["ratio"] >= MIN_CONTRAST, body
        card = measure(page, ".bp_wrapper")
        assert card["bgLum"] < 0.05, card
        assert card["ratio"] >= MIN_CONTRAST, card
        paragraph = measure(page, "main p")
        assert paragraph["ratio"] >= MIN_CONTRAST, paragraph
        assert_no_runtime_errors(errors)

    def test_explicit_choice_wins_over_os_preference(self, server: str, page: Page):
        page.emulate_media(color_scheme="dark")
        page.goto(server + "/Code-Panels/")
        page.evaluate("document.documentElement.setAttribute('data-theme', 'light')")
        assert measure(page, "body")["bgLum"] > 0.8
        page.emulate_media(color_scheme="light")
        page.evaluate("document.documentElement.setAttribute('data-theme', 'dark')")
        assert measure(page, "body")["bgLum"] < 0.05

    def test_code_tokens_are_readable(self, server: str, page: Page):
        page.emulate_media(color_scheme="dark")
        page.goto(server + "/Code-Panels/")
        reports = token_reports(page)
        assert len(reports) >= 3, reports
        failing = [r for r in reports if r["ratio"] < MIN_CONTRAST]
        assert not failing, failing

    def test_table_of_contents_is_readable(self, server: str, page: Page):
        page.emulate_media(color_scheme="dark")
        page.goto(server + "/Code-Panels/")
        link = measure(page, "#toc a")
        assert link["bgLum"] < 0.05, link
        assert link["ratio"] >= MIN_CONTRAST, link
