"""Browser checks for a site generated from compiled-code data (`vbp code-site`).

The site is generated from `code_site_fixture/` (four modules, one with a long dotted name, a
declaration chain a <- b <- c <- d with source occurrences and hover texts). The checks: the
dependency graph's first view is drawn before the page scripts have run and is then laid out
from build-time positions, the ego view around a declaration with its hop count, the node view's
and the chapter entry's neighbourhood links, the highlighted source excerpt's hovers, the search
box finding a declaration, long module names wrapping in the sidebar, and the informal statements
the data gives (`Demo.c` with math, a title and a proof; `Demo.d` with raw HTML and a script link):
the node view shows the statement beside the Lean side, its math typeset when the site was built
and copied from the page's templates (theme colours, keyboard, screen-reader text, narrow
screens), a node without one shows the Lean side alone, and a statement's HTML stays text.
"""

import shutil
import subprocess
import sys
from pathlib import Path

import pytest
from playwright.sync_api import Page

from scripts.blueprint_harness_paths import canonical_test_blueprint_output_dir
from support import PACKAGE_ROOT, find_free_port, wait_for_server, assert_vendored_licenses

FIXTURE = Path(__file__).parent / "code_site_fixture"


def vbp_executable() -> Path:
    exe = PACKAGE_ROOT / ".lake" / "build" / "bin" / "vbp"
    if not exe.exists():
        subprocess.run(["lake", "build", "vbp"], cwd=PACKAGE_ROOT, check=True)
    return exe


@pytest.fixture(scope="session")
def code_site_dir() -> Path:
    output_dir = canonical_test_blueprint_output_dir("code_site_fixture", Path(__file__))
    if output_dir.exists():
        shutil.rmtree(output_dir)
    output_dir.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(
        [str(vbp_executable()), "code-site", "--data", str(FIXTURE / "code-site.json"),
         "--root", str(FIXTURE), "--output", str(output_dir), "--reproducible"],
        cwd=FIXTURE,
        check=True,
    )
    return output_dir / "html-multi"


@pytest.fixture(scope="session")
def code_site_url(code_site_dir: Path):
    port = find_free_port()
    proc = subprocess.Popen(
        [sys.executable, "-m", "http.server", str(port), "--bind", "127.0.0.1"],
        cwd=code_site_dir,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    url = f"http://127.0.0.1:{port}"
    wait_for_server(url, proc)
    yield url
    proc.terminate()
    proc.wait()


def wait_for_interactive_graph(page: Page) -> None:
    page.wait_for_function(
        """() => {
            const node = document.querySelector(".bp_graph_canvas svg g.node");
            const block = document.querySelector(".bp_graph_fullwidth");
            const state = block ? block.__bpGraphState : null;
            return !!node && !!node.__data__ && !!state && state.renderFinalizedToken === state.renderToken;
        }""",
        timeout=60000,
    )


def drawn_labels(page: Page) -> list[str]:
    return page.evaluate(
        """() => Array.from(document.querySelectorAll(".bp_graph_canvas svg g.node text"))
            .map((t) => t.textContent.trim()).sort()"""
    )


def test_first_view_is_drawn_from_build_time_layout(page: Page, code_site_dir: Path, code_site_url: str):
    if shutil.which("dot") is None:
        pytest.skip("Graphviz `dot` is not installed: the generator leaves the layout to the page")
    html = (code_site_dir / "Dependency-Graph" / "index.html").read_text(encoding="utf-8")
    assert '<svg class="bp_graph_prerendered" data-variant="full"' in html
    assert 'class="bp-graph-layout" data-variant="full"' in html
    page.goto(code_site_url + "/Dependency-Graph/", wait_until="domcontentloaded")
    wait_for_interactive_graph(page)
    assert page.locator(".bp_graph_canvas").get_attribute("data-bp-graph-layout-source") == "build"
    assert page.locator(".bp_graph_prerender_overlay").count() == 0
    assert drawn_labels(page) == ["Demo.b", "Demo.c", "Demo.d", "a"]


def test_ego_view_and_hops(page: Page, code_site_url: str):
    page.goto(code_site_url + "/Dependency-Graph/#ego=Demo.b&k=1", wait_until="domcontentloaded")
    wait_for_interactive_graph(page)
    assert page.locator(".bp_graph_view_select").input_value() == "ego"
    assert drawn_labels(page) == ["Demo.b", "Demo.c", "a"]
    assert page.locator(".bp_graph_canvas svg g.node.bp_graph_ego_center").count() == 1
    hops = page.locator(".bp_graph_ego_hops")
    assert hops.is_visible()
    hops.select_option("2")
    page.wait_for_function("document.querySelectorAll('.bp_graph_canvas svg g.node').length === 4")
    wait_for_interactive_graph(page)
    assert page.evaluate("location.hash") == "#ego=Demo.b&k=2"
    page.locator(".bp_graph_view_select").select_option("full")
    page.wait_for_function("!document.querySelector('.bp_graph_ego_hops_label') || document.querySelector('.bp_graph_ego_hops_label').hidden")


def test_node_view_links_to_its_neighbourhood(page: Page, code_site_url: str):
    page.goto(code_site_url + "/Dependency-Graph/#node=Demo.c", wait_until="domcontentloaded")
    page.wait_for_selector(".bp_graph_preview .bp_node_view", timeout=60000)
    link = page.locator(".bp_graph_preview .bp_node_view_header a.bp_node_view_ego")
    assert link.get_attribute("href").endswith("/Dependency-Graph/#ego=Demo.c&k=1")
    link.click()
    page.wait_for_function("document.querySelector('.bp_graph_view_select').value === 'ego'")
    wait_for_interactive_graph(page)
    assert drawn_labels(page) == ["Demo.b", "Demo.c", "Demo.d", "a"]


def test_chapter_entry_highlighted_source_with_hovers(page: Page, code_site_url: str):
    page.goto(code_site_url + "/Demo___A/", wait_until="load")
    assert "The first module." in page.locator("main").inner_text()
    ego = page.locator("a.bp_external_decl_ego").first
    assert ego.get_attribute("href") == "Dependency-Graph/#ego=Demo.a"
    page.evaluate("""() => document.querySelectorAll("details").forEach((d) => { d.open = true; })""")
    source = page.locator(".bp_plain_decl_source pre").first
    assert source.locator(".keyword.token").first.inner_text() == "def"
    nat = source.locator(".const.token[data-verso-hover]").filter(has_text="Nat").first
    nat.scroll_into_view_if_needed()
    nat.hover()
    page.wait_for_selector(".tippy-box", timeout=10000)
    assert "Nat : Type" in page.locator(".tippy-box").first.inner_text()


def test_search_finds_a_declaration(page: Page, code_site_url: str):
    page.goto(code_site_url + "/", wait_until="load")
    page.locator("#cb1-input").click()
    page.keyboard.type("Demo.c")
    page.wait_for_selector("[role=option]", timeout=10000)
    options = page.locator("[role=option]").all_inner_texts()
    assert any("Demo.c" in o and "Documentation" in o for o in options)


def test_long_module_names_wrap_in_the_sidebar(page: Page, code_site_url: str):
    page.set_viewport_size({"width": 1280, "height": 800})
    page.goto(code_site_url + "/", wait_until="load")
    entry = page.locator("#toc a", has_text="ForTheSidebar").first
    assert entry.locator("wbr").count() > 0
    assert page.evaluate(
        """() => {
            const a = Array.from(document.querySelectorAll("#toc a")).find((x) => x.textContent.includes("ForTheSidebar"));
            const cell = a.closest("td");
            return cell.scrollWidth <= cell.clientWidth + 1;
        }"""
    )


STATEMENT = ".bp_graph_preview .bp_node_view .bp_sbs_informal"


def open_stated_node_view(page: Page, code_site_url: str) -> None:
    page.goto(code_site_url + "/Dependency-Graph/#node=Demo.c", wait_until="domcontentloaded")
    page.wait_for_selector(".bp_graph_preview .bp_node_view", timeout=60000)
    page.wait_for_function(
        f"""() => document.querySelectorAll("{STATEMENT} .bp_math_static > svg").length >= 2""",
        timeout=10000,
    )


def test_node_view_shows_the_statement_beside_lean(page: Page, code_site_url: str):
    open_stated_node_view(page, code_site_url)
    view = page.locator(".bp_graph_preview .bp_node_view")
    informal = view.locator(".bp_sbs_informal")
    assert informal.count() == 1
    assert "Gauss's sum" in informal.inner_text()
    assert view.locator(".bp_sbs_formal").count() == 1
    assert view.locator(".bp_sbs_single").count() == 0
    assert view.locator("details.bp_node_view_proof").count() == 1


def test_node_view_statement_math_is_copied_from_the_page(page: Page, code_site_url: str):
    """The statement's formulas were typeset when the site was built: the node view shows
    copies of the page's templates, every reference is replaced, the pictures are drawn from
    the page's glyph set, and KaTeX is neither loaded nor asked for."""
    requested: list[str] = []
    page.on("request", lambda request: requested.append(request.url))
    open_stated_node_view(page, code_site_url)
    facts = page.evaluate(
        f"""() => {{
            const root = document.querySelector("{STATEMENT}");
            const formulas = Array.from(root.querySelectorAll(".bp_math_static"));
            const pictures = Array.from(root.querySelectorAll(".bp_math_static > svg"));
            const ids = Array.from(document.querySelectorAll("[id]")).map((e) => e.id);
            const templates = Array.from(document.querySelectorAll("template.bp_math_stored"));
            return {{
                formulas: formulas.length,
                display: root.querySelectorAll(".bp_math.display.bp_math_static").length,
                references: root.querySelectorAll("code[data-bp-math-key]").length,
                katex: root.querySelectorAll(".katex, .katex-error").length,
                katexLoaded: typeof katex !== "undefined",
                sized: pictures.every((s) => {{
                    const r = s.getBoundingClientRect();
                    return r.width > 0 && r.height > 0;
                }}),
                glyphsFound: pictures.every((s) => Array.from(s.querySelectorAll("use")).every((u) => {{
                    const target = document.getElementById((u.getAttribute("xlink:href") || "").slice(1));
                    return !!target && !!target.closest("svg.bp_math_glyphs");
                }})),
                uses: root.querySelectorAll(".bp_math_static > svg use").length,
                uniqueIds: new Set(ids).size === ids.length,
                templates: templates.length,
                templatesInert: templates.every((t) =>
                    t.content.querySelectorAll("script, iframe, object, embed, img, a, style, link").length === 0 &&
                    Array.from(t.content.querySelectorAll("*")).every((e) =>
                        Array.from(e.attributes).every((a) => !a.name.startsWith("on")))),
                marked: formulas.every((f) => f.getAttribute("data-bp-math-rendered") === "1"),
            }};
        }}"""
    )
    assert facts["formulas"] >= 2 and facts["display"] == 1, facts
    assert facts["references"] == 0 and facts["katex"] == 0 and not facts["katexLoaded"], facts
    assert facts["sized"] and facts["glyphsFound"] and facts["uses"] > 0, facts
    assert facts["uniqueIds"] and facts["templates"] >= 2 and facts["templatesInert"], facts
    assert facts["marked"], facts
    assert not [url for url in requested if "/katex/" in url], requested
    # opening the view again copies the templates again: nothing is used up
    page.goto(code_site_url + "/Dependency-Graph/#node=Demo.d", wait_until="domcontentloaded")
    page.wait_for_selector(".bp_graph_preview .bp_node_view[data-bp-node-view='Demo.d']", timeout=60000)
    page.evaluate("window.location.hash = '#node=Demo.c'")
    page.wait_for_function(
        f"""() => document.querySelectorAll("{STATEMENT} .bp_math_static > svg").length >= 2
            && document.querySelector(".bp_graph_preview .bp_node_view").getAttribute("data-bp-node-view") === 'Demo.c'""",
        timeout=10000,
    )
    assert page.evaluate(
        """() => { const ids = Array.from(document.querySelectorAll("[id]")).map((e) => e.id);
                   return new Set(ids).size === ids.length; }"""
    )


def test_node_view_statement_math_follows_the_theme(page: Page, code_site_url: str):
    """The pictures are drawn in the text colour of the statement, in the light and the dark
    theme."""
    open_stated_node_view(page, code_site_url)
    colours = {}
    for theme in ("light", "dark"):
        page.evaluate(f"document.documentElement.setAttribute('data-theme', '{theme}')")
        colours[theme] = page.evaluate(
            f"""() => {{
                const picture = document.querySelector("{STATEMENT} .bp_math_static > svg");
                const glyph = picture.querySelector("use");
                return {{
                    text: getComputedStyle(picture.closest("p")).color,
                    picture: getComputedStyle(picture).color,
                    fill: getComputedStyle(glyph).fill,
                }};
            }}"""
        )
        assert colours[theme]["picture"] == colours[theme]["text"], colours
        assert colours[theme]["fill"] == colours[theme]["text"], colours
    assert colours["light"]["text"] != colours["dark"]["text"], colours


def test_node_view_statement_math_for_keyboard_and_screen_reader(page: Page, code_site_url: str):
    """A node opened from the keyboard shows the typeset statement; a screen reader gets each
    formula's MathML and not its picture, and copying the statement copies the TeX source."""
    page.goto(code_site_url + "/Dependency-Graph/", wait_until="domcontentloaded")
    wait_for_interactive_graph(page)
    page.evaluate(
        """() => {
            const node = Array.from(document.querySelectorAll(".bp_graph_canvas svg g.node"))
                .find((n) => (n.textContent || "").includes("Demo.c"));
            node.focus();
        }"""
    )
    assert page.evaluate("document.activeElement && document.activeElement.matches('g.node')")
    page.keyboard.press("Enter")
    page.wait_for_function(
        f"""() => document.querySelectorAll("{STATEMENT} .bp_math_static > svg").length >= 2""",
        timeout=20000,
    )
    facts = page.evaluate(
        f"""() => {{
            const root = document.querySelector("{STATEMENT}");
            const formulas = Array.from(root.querySelectorAll(".bp_math_static"));
            const selection = window.getSelection();
            selection.removeAllRanges();
            const range = document.createRange();
            range.selectNodeContents(root);
            selection.addRange(range);
            const copied = selection.toString();
            selection.removeAllRanges();
            return {{
                picturesHidden: formulas.every((f) =>
                    Array.from(f.querySelectorAll(":scope > svg")).every((s) =>
                        s.getAttribute("aria-hidden") === "true" && s.getAttribute("focusable") === "false")),
                mathml: formulas.every((f) => {{
                    const m = f.querySelector(":scope > math.bp_math_mathml");
                    return !!m && !m.hasAttribute("aria-hidden") &&
                        !!m.querySelector("annotation[encoding='application/x-tex']");
                }}),
                sourceHidden: formulas.every((f) => {{
                    const s = f.querySelector(":scope > .bp_math_source");
                    return !!s && s.getAttribute("aria-hidden") === "true" && s.getBoundingClientRect().width <= 1;
                }}),
                sources: formulas.map((f) => f.querySelector(".bp_math_source").textContent),
                copied: copied,
            }};
        }}"""
    )
    assert facts["picturesHidden"] and facts["mathml"] and facts["sourceHidden"], facts
    assert "$n \\in \\NN$" in facts["sources"], facts
    assert "\\in \\NN" in facts["copied"], facts


def test_node_view_statement_math_fits_a_narrow_screen(page: Page, code_site_url: str):
    """On a narrow screen the statement's formulas stay inside the node view: inline pictures
    are no wider than their line, and a display formula scrolls inside its own box."""
    page.set_viewport_size({"width": 390, "height": 800})
    open_stated_node_view(page, code_site_url)
    facts = page.evaluate(
        f"""() => {{
            const root = document.querySelector("{STATEMENT}");
            const box = root.getBoundingClientRect();
            const inline = Array.from(root.querySelectorAll(".bp_math.inline.bp_math_static > svg"));
            const display = root.querySelector(".bp_math.display.bp_math_static");
            const style = getComputedStyle(display);
            return {{
                inlineFits: inline.every((s) => {{
                    const r = s.getBoundingClientRect();
                    return r.left >= box.left - 1 && r.right <= box.right + 1;
                }}),
                displayInside: display.getBoundingClientRect().right <= box.right + 1,
                displayScrolls: style.overflowX === "auto" && style.display === "block",
            }};
        }}"""
    )
    assert facts["inlineFits"] and facts["displayInside"] and facts["displayScrolls"], facts


def test_display_formula_has_the_size_katex_gives_it(page: Page, code_site_url: str):
    """A display formula typeset when the site was built is as large as KaTeX draws the same
    source in its place: the same font size, and the same width and height to a hundredth of
    an em. KaTeX is loaded here from the site's files only to be measured against."""
    page.goto(code_site_url + "/Demo___C/", wait_until="load")
    page.wait_for_selector("main .bp_math.display.bp_math_static > svg", timeout=20000)
    page.add_style_tag(url=code_site_url + "/-verso-data/katex/katex.css")
    page.add_script_tag(url=code_site_url + "/-verso-data/katex/katex.js")
    facts = page.evaluate(
        r"""async () => {
            const formula = document.querySelector("main .bp_math.display.bp_math_static");
            const picture = formula.querySelector(":scope > svg").getBoundingClientRect();
            const em = parseFloat(getComputedStyle(formula).fontSize);
            const source = formula.querySelector(".bp_math_source").textContent
                .replace(/^\\\[/, "").replace(/\\\]$/, "");
            const table = window.bpTexPreludeTable || {};
            const prelude = typeof table.default === "string" ? table.default : "";
            const code = document.createElement("code");
            code.className = "bp_math display";
            formula.after(code);
            katex.render(prelude + "\n" + source, code, { throwOnError: false, displayMode: true });
            await document.fonts.ready;
            const boxes = Array.from(code.querySelectorAll(".katex-html .base"))
                .map((b) => b.getBoundingClientRect());
            const katexEm = parseFloat(getComputedStyle(code.querySelector(".katex")).fontSize);
            const width = Math.max(...boxes.map((b) => b.right)) - Math.min(...boxes.map((b) => b.left));
            const height = Math.max(...boxes.map((b) => b.bottom)) - Math.min(...boxes.map((b) => b.top));
            return {
                errors: code.querySelectorAll(".katex-error").length,
                em: em, katexEm: katexEm,
                // the picture has 0.05 em of padding on every side
                width: picture.width / em - 0.1, height: picture.height / em - 0.1,
                katexWidth: width / katexEm, katexHeight: height / katexEm,
            };
        }"""
    )
    assert facts["errors"] == 0, facts
    assert abs(facts["em"] - facts["katexEm"]) < 0.01, facts
    assert abs(facts["width"] - facts["katexWidth"]) < 0.01, facts
    assert abs(facts["height"] - facts["katexHeight"]) < 0.01, facts


def test_node_view_without_a_statement_is_lean_only(page: Page, code_site_url: str):
    page.goto(code_site_url + "/Dependency-Graph/#node=Demo.b", wait_until="domcontentloaded")
    page.wait_for_selector(".bp_graph_preview .bp_node_view", timeout=60000)
    view = page.locator(".bp_graph_preview .bp_node_view")
    assert view.locator(".bp_sbs_informal").count() == 0
    assert view.locator(".bp_sbs_single").count() == 1
    assert view.locator(".bp_sbs_formal").count() == 1


def test_statement_html_stays_text(page: Page, code_site_url: str):
    page.goto(code_site_url + "/Demo___Some___Very___Long___Module___Name___ForTheSidebar/", wait_until="load")
    main = page.locator("main").inner_text()
    assert "<script>window.__bpStatementRan = true</script>" in main
    assert page.evaluate("window.__bpStatementRan === undefined")
    assert page.locator("main a[href^='javascript:']").count() == 0
    assert page.locator("main .bp_math_static > svg").count() >= 1
    assert page.locator("main .katex").count() == 0


def test_contents_backdrop_closes_the_panel(page: Page, code_site_url: str):
    page.set_viewport_size({"width": 600, "height": 800})
    page.goto(code_site_url + "/Demo___A/", wait_until="load")
    page.wait_for_function(
        """() => { const b = document.querySelector(".toc-backdrop");
                   return !!b && !b.hasAttribute("onclick"); }""",
        timeout=10000,
    )
    page.locator("#toggle-toc-click").click()
    assert page.evaluate("document.getElementById('toggle-toc').checked")
    page.locator(".toc-backdrop").click(position={"x": 560, "y": 400})
    assert not page.evaluate("document.getElementById('toggle-toc').checked")


def test_code_site_ships_vendored_licences(code_site_dir: Path):
    assert_vendored_licenses(code_site_dir)
