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


# Per rendered status node of the dependency graph: its fill, border and label colours, the
# status tokens they should come from, and the label's contrast against the fill. Status classes
# name their tokens: `bp_graph_status_ready` -> `--bp-color-status-ready`,
# `bp_graph_statement_ready` -> `--bp-color-status-ready-border`.
GRAPH_NODE_REPORTS = """
() => {
""" + COLOR_HELPERS + """
  const probe = document.createElement('span');
  document.body.appendChild(probe);
  const tokenColor = (name) => {
    probe.style.color = 'var(' + name + ')';
    return parse(getComputedStyle(probe).color);
  };
  const graphBg = document.querySelector('.bp_graph_canvas svg g.graph > polygon');
  const bg = graphBg ? parse(getComputedStyle(graphBg).fill) : null;
  const out = [];
  for (const node of document.querySelectorAll('.bp_graph_canvas svg g.node')) {
    const fillClass = [...node.classList].find((c) => c.startsWith('bp_graph_status_'));
    if (!fillClass) continue;
    const borderClass = [...node.classList].find((c) => c.startsWith('bp_graph_statement_'));
    const shape = node.querySelector('ellipse, polygon, path');
    const text = node.querySelector('text');
    if (!shape || !text) continue;
    const fill = parse(getComputedStyle(shape).fill);
    const stroke = parse(getComputedStyle(shape).stroke);
    const ink = parse(getComputedStyle(text).fill);
    const fillToken = '--bp-color-status-' + fillClass.slice('bp_graph_status_'.length).replace(/_/g, '-');
    const borderToken = borderClass
      ? '--bp-color-status-' + borderClass.slice('bp_graph_statement_'.length).replace(/_/g, '-') + '-border'
      : fillToken + '-border';
    out.push({
      node: node.id, fillClass, borderClass, fill, stroke, ink, bg,
      fillToken: tokenColor(fillToken), borderToken: tokenColor(borderToken),
      labelRatio: contrast(ink, fill), borderRatio: bg ? contrast(stroke, bg) : null,
    });
  }
  probe.remove();
  return out;
}
"""

MIN_BORDER_CONTRAST = 3.0


def same_rgb(a: dict, b: dict) -> bool:
    return all(abs(a[k] - b[k]) < 1 for k in ("r", "g", "b"))


def graph_node_reports(page: Page, server: str, scheme: str) -> list[dict]:
    page.emulate_media(color_scheme=scheme)
    page.goto(server + "/Dependency-Graph/", wait_until="domcontentloaded", timeout=60000)
    page.wait_for_function(
        "() => document.querySelectorAll('.bp_graph_canvas svg g.node[class*=\"bp_graph_status_\"]').length > 0",
        timeout=60000,
    )
    return page.evaluate(GRAPH_NODE_REPORTS)


class TestGraphStatusColours:
    def test_light_graph_nodes_use_the_status_tokens(self, server: str, page: Page):
        reports = graph_node_reports(page, server, "light")
        assert reports
        assert reports[0]["bg"] and lum_of(reports[0]["bg"]) > 0.8, reports[0]
        for r in reports:
            assert same_rgb(r["fill"], r["fillToken"]), r
            assert same_rgb(r["stroke"], r["borderToken"]), r
            assert r["labelRatio"] >= MIN_CONTRAST, r

    def test_dark_graph_nodes_use_the_status_tokens(self, server: str, page: Page):
        reports = graph_node_reports(page, server, "dark")
        assert reports
        assert reports[0]["bg"] and lum_of(reports[0]["bg"]) < 0.05, reports[0]
        for r in reports:
            assert same_rgb(r["fill"], r["fillToken"]), r
            assert same_rgb(r["stroke"], r["borderToken"]), r
            assert r["labelRatio"] >= MIN_CONTRAST, r
            assert r["borderRatio"] >= MIN_BORDER_CONTRAST, r


def lum_of(c: dict) -> float:
    def f(v: float) -> float:
        v /= 255
        return v / 12.92 if v <= 0.03928 else ((v + 0.055) / 1.055) ** 2.4

    return 0.2126 * f(c["r"]) + 0.7152 * f(c["g"]) + 0.0722 * f(c["b"])
