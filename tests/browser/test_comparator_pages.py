"""Browser checks of the Comparator pages (`Informal.Commands.Comparator`).

Sites are generated from `comparator_site_fixture/`, a small library and three Comparator
challenges in the layout `Comparator/<Name>/` (no dependencies), built here with the toolchain's
own `lake` and replayed by the kernel checkers:

* `Double`: the honest solution, accepted by the replay;
* `Differs`: a solution whose Lean statement differs from the challenge's;
* `Pending`: a challenge the project does not build, so it is not compared;

and once more with the forged solution of `comparator_site_fixture/forged/` in `Double` (no
`sorry`, no axiom, and a constant no kernel saw), which the replay rejects. A copy whose
challenge folder holds a stray file is not generated, and says why.

The pages are read in the light and the dark theme, at 1280 and 360 pixels, with the keyboard
and without scripts; every verdict they show must be the Project Stats page's, the files must be
shown in full and escaped, and no request may leave the site.
"""

import json
import shutil
import subprocess
import sys
from pathlib import Path

import pytest
from playwright.sync_api import Page

from scripts.blueprint_harness_paths import canonical_test_blueprint_output_dir
from support import PACKAGE_ROOT, find_free_port, wait_for_server
from test_dark_theme_runtime import COLOR_HELPERS, MIN_CONTRAST
from test_project_stats_runtime import CHIP_REPORTS, check_chips, check_focus_rings, check_one_face

FIXTURE = Path(__file__).parent / "comparator_site_fixture"
SCHEMES = ("light", "dark")


def vbp_executable() -> Path:
    exe = PACKAGE_ROOT / ".lake" / "build" / "bin" / "vbp"
    if not exe.exists():
        subprocess.run(["lake", "build", "vbp"], cwd=PACKAGE_ROOT, check=True)
    return exe


def build_project(root: Path, forged: bool) -> None:
    if root.exists():
        shutil.rmtree(root)
    shutil.copytree(FIXTURE, root)
    if forged:
        shutil.copy(FIXTURE / "forged" / "Solution.lean", root / "Comparator" / "Double" / "Solution.lean")
        shutil.copy(FIXTURE / "forged" / "code-site.json", root / "code-site.json")
    shutil.rmtree(root / "forged")
    shutil.copy(PACKAGE_ROOT / "lean-toolchain", root / "lean-toolchain")
    subprocess.run(["lake", "build"], cwd=root, check=True)


def generate(root: Path, out: Path) -> subprocess.CompletedProcess:
    if out.exists():
        shutil.rmtree(out)
    # through `lake env`, which names the toolchain whose checkers replay the modules
    return subprocess.run(
        ["lake", "env", str(vbp_executable()), "code-site", "--data", str(root / "code-site.json"),
         "--root", str(root), "--output", str(out), "--reproducible"],
        cwd=root, capture_output=True, text=True,
    )


@pytest.fixture(scope="session")
def comparator_sites() -> dict[str, Path]:
    if shutil.which("lake") is None:
        pytest.skip("no `lake` to compile the fixture project")
    base = canonical_test_blueprint_output_dir("comparator_site_fixture", Path(__file__))
    base.parent.mkdir(parents=True, exist_ok=True)
    sites = {}
    for state, forged in (("accepted", False), ("rejected", True)):
        root = base / f"project-{state}"
        build_project(root, forged)
        out = base / f"site-{state}"
        result = generate(root, out)
        assert result.returncode == 0, result.stderr
        sites[state] = out / "html-multi"
    return sites


@pytest.fixture(scope="session")
def comparator_urls(comparator_sites: dict[str, Path]):
    procs, urls = [], {}
    for state, site in comparator_sites.items():
        port = find_free_port()
        proc = subprocess.Popen(
            [sys.executable, "-m", "http.server", str(port), "--bind", "127.0.0.1"],
            cwd=site, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        )
        urls[state] = f"http://127.0.0.1:{port}"
        wait_for_server(urls[state], proc)
        procs.append(proc)
    yield urls
    for proc in procs:
        proc.terminate()
        proc.wait()


def watch(page: Page, base: str) -> dict[str, list[str]]:
    """Console errors, page errors and requests that leave the site, collected as the page runs."""
    seen: dict[str, list[str]] = {"errors": [], "outside": []}
    page.on("pageerror", lambda exc: seen["errors"].append(str(exc)))
    page.on("console", lambda m: seen["errors"].append(m.text) if m.type == "error" else None)
    page.on("request", lambda r: seen["outside"].append(r.url)
            if not r.url.startswith(base) and not r.url.startswith("data:") else None)
    return seen


def verdicts(page: Page, scope: str) -> dict[str, tuple[str, str]]:
    return page.evaluate(
        """(scope) => Object.fromEntries(Array.from(document.querySelectorAll(scope + " [data-bp-theorem]"))
            .map((e) => [e.getAttribute("data-bp-theorem"),
                         [e.getAttribute("data-bp-verdict"),
                          (e.querySelector(".bp_stats_verdict") || {}).textContent || ""]]))""",
        scope,
    )


@pytest.mark.parametrize("scheme", SCHEMES)
def test_index_lists_every_challenge_with_the_stats_page_verdicts(page: Page, comparator_urls, scheme):
    url = comparator_urls["accepted"]
    seen = watch(page, url)
    page.emulate_media(color_scheme=scheme)
    page.goto(url + "/Comparator/", wait_until="load")
    names = page.eval_on_selector_all(".bp_comparator_index_item", "els => els.map(e => e.dataset.bpChallenge)")
    assert names == ["Differs", "Double", "Pending"]
    index = verdicts(page, ".bp_comparator_index")
    assert index["Cmp.double_even"][0] == "proved"
    assert index["Dif.add_swap"][0] == "differs"
    pending = page.locator('.bp_comparator_index_item[data-bp-challenge="Pending"]').inner_text()
    assert "Not compared: the challenge module has not been built (Comparator.Pending.Challenge)." in pending
    page.goto(url + "/Project-Stats/", wait_until="load")
    assert verdicts(page, ".bp_project_stats") == index
    bands = page.eval_on_selector_all(".bp_stats_headline .bp_stats_band_title", "els => els.map(e => e.textContent)")
    assert bands == ["Headline result: Differs", "Headline result: Double", "Headline result: Pending"]
    assert page.locator(".bp_stats_challenge_link").count() == 3
    assert seen == {"errors": [], "outside": []}


@pytest.mark.parametrize("scheme", SCHEMES)
def test_challenge_page_shows_files_verdict_and_links(page: Page, comparator_urls, scheme):
    url = comparator_urls["accepted"]
    seen = watch(page, url)
    page.emulate_media(color_scheme=scheme)
    page.goto(url + "/Comparator/Double/", wait_until="load")
    assert verdicts(page, ".bp_comparator_page") == {"Cmp.double_even": ["proved", "Lean statement proved"]}
    text = page.locator(".bp_comparator_page").inner_text()
    challenge = (FIXTURE / "Comparator" / "Double" / "Challenge.lean").read_text(encoding="utf-8")
    solution = (FIXTURE / "Comparator" / "Double" / "Solution.lean").read_text(encoding="utf-8")
    # each Lean file in full, line by line, as highlighted Lean
    shown = page.eval_on_selector_all(
        ".bp_comparator_code code.hl.lean",
        "els => els.map(e => Array.from(e.querySelectorAll('.bp_code_line')).map(l => l.textContent).join('\\n'))",
    )
    assert [s.strip() for s in shown] == [challenge.strip(), solution.strip()]
    assert page.locator(".bp_comparator_code .keyword.token").count() > 0
    config = page.locator(".bp_comparator_config code").inner_text()
    assert json.loads(config) == json.loads(
        (FIXTURE / "Comparator" / "Double" / "comparator.json").read_text(encoding="utf-8"))
    assert "For every natural number n, the number 2n is even." in text  # the author's claim
    assert "What a verdict of the kernel replay leaves trusted" in text
    assert page.locator(".bp_comparator_graph_link").get_attribute("href").endswith(
        "#ego=Cmp.double_even&k=1")
    assert page.locator(".bp_comparator_stats_link").count() == 1
    # outside GitHub Actions no run is linked
    assert page.locator(".bp_comparator_ci_link").count() == 0
    # the background of the code follows the theme
    background = page.evaluate("getComputedStyle(document.querySelector('.bp_comparator_code')).backgroundColor")
    body = page.evaluate("getComputedStyle(document.body).backgroundColor")
    assert background and body
    assert seen == {"errors": [], "outside": []}


def test_hovers_on_the_solution(page: Page, comparator_urls):
    url = comparator_urls["accepted"]
    page.goto(url + "/Comparator/Double/", wait_until="load")
    hovered = page.locator("#solution-file [data-verso-hover]")
    assert hovered.count() > 0
    # the keyboard reaches every token with a hover, and focusing one shows its hover
    assert page.locator("#solution-file [data-verso-hover]:not([tabindex='0'])").count() == 0
    page.locator("#solution-file .bp_comparator_code [data-verso-hover]").first.focus()
    page.wait_for_selector(".tippy-box", state="visible", timeout=5000)
    assert page.locator(".tippy-box").first.inner_text().strip()


def test_differing_solution_is_escaped_and_never_proved(page: Page, comparator_urls):
    url = comparator_urls["accepted"]
    page.goto(url + "/Comparator/Differs/", wait_until="load")
    found = verdicts(page, ".bp_comparator_page")
    assert found["Dif.add_swap"][0] == "differs"
    html = page.content()
    assert "&lt;b&gt;not&lt;/b&gt;" in html and "<b>not</b>" not in html
    assert "Lean statement proved" not in page.locator(".bp_comparator_page").inner_text()


def test_forged_solution_is_rejected_everywhere(page: Page, comparator_urls):
    url = comparator_urls["rejected"]
    for path in ("/Comparator/", "/Comparator/Double/", "/Project-Stats/"):
        page.goto(url + path, wait_until="load")
        found = verdicts(page, "main")
        assert found["Cmp.double_even"][0] == "rejected", (path, found)
        # no verdict says proved (the explanation of the marks on the stats page names the words)
        assert page.locator(".bp_stats_verdict_proved").count() == 0, path


def test_narrow_window_keyboard_and_no_sideways_scroll(page: Page, comparator_urls):
    url = comparator_urls["accepted"]
    page.set_viewport_size({"width": 360, "height": 800})
    page.goto(url + "/Comparator/Double/", wait_until="load")
    sideways = page.evaluate("document.documentElement.scrollWidth - document.documentElement.clientWidth")
    assert sideways <= 1
    # the links of the page are reached with the keyboard, and the focus is visible
    link = page.locator(".bp_comparator_stats_link")
    link.focus()
    assert page.evaluate("document.activeElement.classList.contains('bp_comparator_stats_link')")
    outline = page.evaluate("getComputedStyle(document.activeElement).outlineStyle")
    assert outline != "none"


def test_pages_read_about_the_page_axis(page: Page, comparator_urls):
    url = comparator_urls["accepted"]
    # wide enough that the Comparator content is narrower than the content area
    page.set_viewport_size({"width": 1920, "height": 900})
    for path, selectors in (("/Comparator/", ("h1", ".bp_comparator_intro", "ol.section-toc")),
                            ("/Comparator/Double/", ("h1", ".bp_comparator_intro"))):
        page.goto(url + path, wait_until="load")
        offsets = page.evaluate(
            """(selectors) => {
                const area = document.querySelector('main .content-wrapper > section').getBoundingClientRect();
                const axis = (area.left + area.right) / 2;
                return selectors.map((s) => {
                    const e = document.querySelector('main .content-wrapper > section ' + s);
                    const b = e.getBoundingClientRect();
                    return [s, (b.left + b.right) / 2 - axis];
                });
            }""",
            list(selectors),
        )
        assert all(abs(offset) <= 1 for _, offset in offsets), (path, offsets)


def test_pages_without_scripts(browser, comparator_sites):
    from conftest import serve_site

    context = browser.new_context(java_script_enabled=False)
    try:
        page = context.new_page()
        with serve_site(comparator_sites["accepted"]) as url:
            page.goto(url + "/Comparator/Double/", wait_until="domcontentloaded")
            assert page.locator(".bp_comparator_code code.hl.lean").count() == 2
            assert page.locator('[data-bp-verdict="proved"]').count() == 1
    finally:
        context.close()


def test_project_off_the_layout_is_not_generated(tmp_path_factory):
    if shutil.which("lake") is None:
        pytest.skip("no `lake`")
    root = tmp_path_factory.mktemp("comparator-off-layout") / "project"
    shutil.copytree(FIXTURE, root)
    shutil.rmtree(root / "forged")
    (root / "Comparator" / "Double" / "notes.md").write_text("x", encoding="utf-8")
    shutil.copy(PACKAGE_ROOT / "lean-toolchain", root / "lean-toolchain")
    result = generate(root, root / "_out")
    assert result.returncode != 0
    assert ("Comparator/Double/notes.md: rule F1 (the files of a challenge): a challenge's folder "
            "holds only Challenge.lean, Solution.lean, comparator.json; move or remove notes.md") \
        in result.stderr
    assert not (root / "_out" / "html-multi").exists()


@pytest.mark.parametrize("path", ["/Project-Stats/", "/Comparator/Double/"])
@pytest.mark.parametrize("width", [1280, 360])
def test_badges_are_aligned_links_in_one_face(page: Page, comparator_urls, path, width):
    url = comparator_urls["accepted"]
    seen = watch(page, url)
    page.set_viewport_size({"width": width, "height": 900})
    page.goto(url + path, wait_until="load")
    check_chips(page.evaluate(CHIP_REPORTS))
    check_one_face(page)
    # every standard axiom of the judged theorem's proof links to the Lean Language Reference
    axioms = page.eval_on_selector_all(
        ".bp_stats_axiom", "els => els.map(e => [e.tagName, e.dataset.bpAxiomClass, e.textContent])")
    for tag, cls, _ in axioms:
        assert (tag == "A") == (cls == "standard"), axioms
    sideways = page.evaluate("document.documentElement.scrollWidth - document.documentElement.clientWidth")
    assert sideways <= 1
    # nothing is fetched from outside the site: the links only point there
    assert seen == {"errors": [], "outside": []}


@pytest.mark.parametrize("path", ["/Project-Stats/", "/Comparator/", "/Comparator/Double/"])
def test_verdicts_link_to_their_explanation(page: Page, comparator_urls, path):
    url = comparator_urls["accepted"]
    page.goto(url + path, wait_until="load")
    links = page.eval_on_selector_all(
        ".bp_stats_verdict_link", "els => els.map(e => [e.href, e.querySelector('.bp_stats_verdict').textContent])")
    assert links
    for href, words in links:
        target, fragment = href.split("#")
        assert target.rstrip("/").endswith("/Project-Stats"), href
        page.goto(href, wait_until="load")
        entry = page.evaluate(
            "(id) => { const e = document.getElementById(id);"
            " return e && e.closest('.bp_stats_meaning_list') ? [e.tagName, e.textContent] : null; }",
            fragment)
        assert entry and entry[0] == "DT", (href, words, entry)
        page.goto(url + path, wait_until="load")


def test_names_and_files_link_to_the_challenge_page(page: Page, comparator_urls):
    url = comparator_urls["accepted"]
    page.goto(url + "/Project-Stats/", wait_until="load")
    hrefs = page.eval_on_selector_all(
        '[data-bp-challenge="Double"] :is(.bp_stats_theorem_name_link, .bp_stats_file_link)',
        "els => els.map(e => e.href)")
    assert len(hrefs) == 3, hrefs
    for href in hrefs:
        target, fragment = href.split("#")
        assert target.rstrip("/").endswith("/Comparator/Double"), href
        assert fragment in ("challenge-file", "solution-file"), href
        page.goto(href, wait_until="load")
        assert page.locator(f"section#{fragment}").count() == 1, href
    # the statement is highlighted, and reads as the challenge states it
    page.goto(url + "/Project-Stats/", wait_until="load")
    code = page.locator('[data-bp-challenge="Double"] .bp_stats_statement_code code.hl.lean')
    assert code.count() == 1
    assert code.locator(".keyword.token").count() > 0
    assert " ".join(code.inner_text().split()) == "theorem double_even (n : Nat) : double n % 2 = 0"


@pytest.mark.parametrize("scheme", SCHEMES)
def test_badges_are_readable(page: Page, comparator_urls, scheme):
    url = comparator_urls["accepted"]
    page.emulate_media(color_scheme=scheme)
    for path in ("/Project-Stats/", "/Comparator/Double/"):
        page.goto(url + path, wait_until="load")
        reports = page.evaluate(
            """(sels) => {""" + COLOR_HELPERS + """
              const out = [];
              for (const el of document.querySelectorAll(sels)) {
                if (!el.textContent.trim()) continue;
                out.push(Object.assign({ text: el.textContent.trim().slice(0, 40) }, report(el)));
              }
              return out; }""",
            ".bp_stats_chip, .bp_stats_axiom, .bp_stats_verdict, .bp_stats_caption, "
            ".bp_stats_fact_label, .bp_stats_theorem_node a, .bp_stats_challenge_link, .bp_stats_axioms_note")
        assert reports
        failing = [r for r in reports if r["ratio"] < MIN_CONTRAST]
        assert not failing, (path, failing)


# Each judged theorem's name: its lines (by the tops of its characters' boxes), and where its
# verdict sits against it.
NAME_LINES = """
() => [...document.querySelectorAll('.bp_stats_theorem_head, .bp_comparator_verdict')].map((head) => {
  const name = head.querySelector('.bp_stats_theorem_name');
  const pill = head.querySelector('.bp_stats_verdict');
  const lines = [];
  const walker = document.createTreeWalker(name, NodeFilter.SHOW_TEXT);
  for (let node = walker.nextNode(); node; node = walker.nextNode()) {
    for (let i = 0; i < node.length; i++) {
      const range = document.createRange();
      range.setStart(node, i);
      range.setEnd(node, i + 1);
      const top = Math.round(range.getBoundingClientRect().top);
      if (!lines.length || Math.abs(lines[lines.length - 1].top - top) > 2) lines.push({ top, text: '' });
      lines[lines.length - 1].text += node.data[i];
    }
  }
  const n = name.getBoundingClientRect(), p = pill.getBoundingClientRect();
  return { lines: lines.map((l) => l.text), nameRight: n.right, nameTop: n.top, nameBottom: n.bottom,
           pillLeft: p.left, pillTop: p.top, pillBottom: p.bottom,
           gap: parseFloat(getComputedStyle(head).columnGap) || 0 };
})
"""


@pytest.mark.parametrize("path", ["/Project-Stats/", "/Comparator/", "/Comparator/Differs/",
                                  "/Comparator/Double/"])
def test_names_stay_whole_and_verdicts_sit_beside_them(page: Page, comparator_urls, path):
    url = comparator_urls["accepted"]
    page.goto(url + path, wait_until="load")
    for width in range(320, 1701, 20):
        page.set_viewport_size({"width": width, "height": 900})
        heads = page.evaluate(NAME_LINES)
        assert heads, path
        for h in heads:
            # one line, or lines that break only after a dot
            assert all(line.endswith(".") for line in h["lines"][:-1]), (width, h)
            # the verdict comes right after the name on its line, or starts a line of its own
            beside = h["pillTop"] < h["nameBottom"] and h["pillBottom"] > h["nameTop"]
            if beside:
                assert h["pillLeft"] - h["nameRight"] <= h["gap"] + 12, (width, h)


def test_statement_is_cut_from_the_challenge_page_code(page: Page, comparator_urls):
    """The statement on the stats page is the challenge's code as its page highlights it, token for
    token, with no tab stop per token. (The fixture's data has no hovers for the challenge module;
    `BlueprintStatsPage` checks that the cut keeps them.)"""
    url = comparator_urls["accepted"]
    page.goto(url + "/Comparator/Double/", wait_until="load")
    tokens = page.eval_on_selector_all(
        "#challenge-file .bp_code_line", """lines => lines.map((l) => l.textContent)""")
    line = next(l for l in tokens if l.startswith("theorem double_even"))
    page.goto(url + "/Project-Stats/", wait_until="load")
    code = page.locator('[data-bp-challenge="Double"] .bp_stats_statement_code code')
    assert code.inner_text().strip() == line.split(" := ")[0]
    assert code.locator(".keyword.token").count() > 0
    assert page.locator(".bp_stats_statement_code [tabindex]").count() == 0


@pytest.mark.parametrize("scheme", SCHEMES)
@pytest.mark.parametrize("path", ["/Project-Stats/", "/Comparator/", "/Comparator/Double/"])
def test_links_of_the_bands_share_one_focus_ring(page: Page, comparator_urls, scheme, path):
    url = comparator_urls["accepted"]
    page.emulate_media(color_scheme=scheme)
    page.goto(url + path, wait_until="load")
    check_focus_rings(page)


def test_index_cards_and_their_page(page: Page, comparator_urls):
    url = comparator_urls["accepted"]
    page.set_viewport_size({"width": 1440, "height": 900})
    page.goto(url + "/Comparator/", wait_until="load")
    # Verso's list of the pages below does not repeat the cards
    assert page.locator("main .section-toc").evaluate_all(
        "els => els.filter((e) => getComputedStyle(e).display !== 'none').length") == 0
    # the command and the option of the first paragraph are code, and do not break
    codes = page.eval_on_selector_all(".bp_comparator_intro code", "els => els.map((e) => e.textContent)")
    assert codes == ["lake comparator", "--config Comparator/<Name>/comparator.json"]
    for code in page.locator(".bp_comparator_intro code").all():
        assert len(code.evaluate("(e) => [...e.getClientRects()].map((r) => r.top)")) == 1
    # the theorem's name links to its challenge's file
    href = page.locator('[data-bp-theorem="Cmp.double_even"] .bp_stats_theorem_name_link').get_attribute("href")
    assert href.endswith("Comparator/Double/#challenge-file"), href
    # the card's title is a link in the structure face, not the text face
    title = page.locator(".bp_comparator_index_title").first
    assert title.evaluate("(e) => getComputedStyle(e).fontFamily") == page.evaluate(
        "getComputedStyle(document.querySelector('.bp_stats_verdict')).fontFamily")


@pytest.mark.parametrize("path", ["/Project-Stats/", "/Comparator/Differs/", "/Comparator/Double/"])
def test_axioms_note_sits_beside_the_chips(page: Page, comparator_urls, path):
    url = comparator_urls["accepted"]
    page.set_viewport_size({"width": 1440, "height": 900})
    page.goto(url + path, wait_until="load")
    rows = page.evaluate("""() => [...document.querySelectorAll('.bp_stats_axioms')]
        .filter((row) => row.querySelector('.bp_stats_axioms_note'))
        .map((row) => {
          const chips = row.querySelector('.bp_stats_axiom_list').getBoundingClientRect();
          const note = row.querySelector('.bp_stats_axioms_note').getBoundingClientRect();
          return { chipsTop: chips.top, chipsBottom: chips.bottom, noteTop: note.top };
        })""")
    assert rows
    for r in rows:
        assert r["chipsTop"] - 1 <= r["noteTop"] <= r["chipsBottom"], r


def test_trusted_sentence_takes_the_measure(page: Page, comparator_urls):
    url = comparator_urls["accepted"]
    page.set_viewport_size({"width": 1440, "height": 900})
    page.goto(url + "/Comparator/Double/", wait_until="load")
    width, size = page.evaluate("""() => { const p = document.querySelector('.bp_comparator_trusted_body p');
        return [p.getBoundingClientRect().width, parseFloat(getComputedStyle(p).fontSize)]; }""")
    assert width <= 40 * size + 1, (width, size)


def test_verdicts_link_to_the_entry_that_explains_them(page: Page, comparator_urls):
    url = comparator_urls["accepted"]
    page.goto(url + "/Project-Stats/", wait_until="load")
    targets = page.eval_on_selector_all(
        "[data-bp-verdict]",
        "els => els.map((e) => [e.getAttribute('data-bp-verdict'), (e.querySelector('.bp_stats_verdict_link') || {}).hash])")
    expected = {"proved": "#bp-meaning-lean-statement-proved", "differs": "#bp-meaning-lean-statement-proved",
                "rejected": "#bp-meaning-kernel-replay", "not-replayed": "#bp-meaning-kernel-replay"}
    assert targets
    for token, hash_ in targets:
        if token in expected:
            assert hash_ == expected[token], (token, hash_)
