"""Browser checks that a site's success colours follow its kernel replay.

Green is a statement: it is drawn only where a kernel replay accepted the Lean code concerned.
Three sites are generated from `replay_site_fixture/` (a small library and a Comparator challenge
with its solution, no dependencies), built here with the toolchain's own `lake`:

* `accepted`: the honest solution, replayed and accepted by both checkers;
* `rejected`: the forged solution of `replay_site_fixture/forged/` (no `sorry`, no axiom, and a
  constant no kernel saw), which the replay rejects;
* `none`: the honest solution, generated without a replay;
* `axiom`: the honest solution and a theorem that rests on an axiom of the project, which is left
  out of the replay while the rest is accepted: the counts are grey, and their words say that the
  replay accepted the build and name the axiom, never that nothing was replayed.

Each site is read in the light and in the dark theme. On the accepted site the headline's
verdict, the progress bar, the summary's cards, the graph's nodes and legend and the node view's
check mark have the success colours; on the other two no element of any page has a greenish
computed colour (highlighted Lean code aside), the bars, cards and fills are the neutral ones, and
the words beside the counts and legend entries say what they rest on.
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

FIXTURE = Path(__file__).parent / "replay_site_fixture"
STATES = ("accepted", "rejected", "none")
SCHEMES = ("light", "dark")

# The values of `Informal.StatusColors` the pages must compute: (light, dark).
ACCEPTED_FILL = ("rgb(22, 101, 52)", "rgb(21, 128, 61)")
ACCEPTED_BORDER = ("rgb(22, 163, 74)", "rgb(74, 222, 128)")
REPORTED_FILL = ("rgb(100, 116, 139)", "rgb(100, 116, 139)")
REPORTED_BORDER = ("rgb(100, 116, 139)", "rgb(148, 163, 184)")
REPORTED_NOTE = "as the compiled files report, not replayed by a kernel"
REJECTED_NOTE = "a kernel checker rejected this build"

PAGES = ("/", "/Project-Stats/", "/Blueprint-Summary/", "/Comparator___Double___Solution/", "/Demo___Basic/")

# Every element (and its ::before / ::after) with a greenish computed colour, as
# "selector property value". Tokens of highlighted Lean code are syntax colours, not statuses.
GREEN_SCAN = """() => {
    const green = (c) => {
        const m = c && c.match(/rgba?\\(([\\d.]+), ([\\d.]+), ([\\d.]+)(?:, ([\\d.]+))?\\)/);
        if (!m) return false;
        const [r, g, b, a] = [+m[1], +m[2], +m[3], m[4] === undefined ? 1 : +m[4]];
        return a > 0 && g > r + 25 && g > b + 25;
    };
    const found = [];
    for (const e of document.querySelectorAll("body *")) {
        if (e.closest(".hl.lean, code, pre")) continue;
        for (const pseudo of [null, "::before", "::after"]) {
            const cs = getComputedStyle(e, pseudo);
            if (pseudo && (cs.content === "none" || cs.content === "normal")) continue;
            for (const prop of ["color", "backgroundColor", "borderTopColor", "borderLeftColor", "fill", "stroke"]) {
                if (prop.startsWith("border") && parseFloat(cs[prop.replace("Color", "Width")]) === 0) continue;
                if (prop === "color" && !pseudo && !e.textContent.trim()) continue;
                if (green(cs[prop])) {
                    found.push(`${e.tagName.toLowerCase()}.${e.getAttribute("class") || ""}${pseudo || ""} ${prop} ${cs[prop]}`);
                }
            }
        }
    }
    return found;
}"""


def vbp_executable() -> Path:
    exe = PACKAGE_ROOT / ".lake" / "build" / "bin" / "vbp"
    if not exe.exists():
        subprocess.run(["lake", "build", "vbp"], cwd=PACKAGE_ROOT, check=True)
    return exe


# A theorem of `Demo.Basic` that rests on an axiom of the project, after the module's own text.
AXIOM_SOURCE = """
axiom Demo.assumed (n : Nat) : Demo.double n = n + n

theorem Demo.double_eq' (n : Nat) : Demo.double n = n + n := Demo.assumed n
"""


def add_axiom(root: Path) -> None:
    """Adds `AXIOM_SOURCE` to the copy at `root`, with its two declarations in the site's data."""
    basic = root / "Demo" / "Basic.lean"
    first = len(basic.read_text(encoding="utf-8").splitlines()) + 1
    basic.write_text(basic.read_text(encoding="utf-8") + AXIOM_SOURCE, encoding="utf-8")

    def declaration(name: str, kind: str, line: int, signature: str, status: str,
                    axioms: list[str]) -> dict:
        span = {"start": {"line": line, "character": 0}, "end": {"line": line, "character": 10}}
        return {"attrs": [], "axioms": axioms, "display": name, "doc": None, "isPrivate": False,
                "kind": kind, "name": name, "range": span, "selection": span,
                "signature": signature, "status": status,
                "uses": [{"kind": "statement", "name": "Demo.double"}]}

    data = json.loads((root / "code-site.json").read_text(encoding="utf-8"))
    module = next(m for m in data["modules"] if m["module"] == "Demo.Basic")
    module["declarations"] += [
        declaration("Demo.assumed", "axiom", first, "Demo.assumed (n : Nat) : Demo.double n = n + n",
                    "axiom", ["Demo.assumed"]),
        declaration("Demo.double_eq'", "theorem", first + 2,
                    "Demo.double_eq' (n : Nat) : Demo.double n = n + n", "proved", ["Demo.assumed"])]
    (root / "code-site.json").write_text(json.dumps(data), encoding="utf-8")


def build_project(root: Path, forged: bool, axiom: bool = False) -> None:
    """A copy of the fixture project at `root`, compiled; `forged` puts the forged solution in,
    `axiom` a theorem that rests on an axiom of the project."""
    if root.exists():
        shutil.rmtree(root)
    shutil.copytree(FIXTURE, root)
    if forged:
        shutil.copy(FIXTURE / "forged" / "Solution.lean", root / "Comparator" / "Double" / "Solution.lean")
        shutil.copy(FIXTURE / "forged" / "code-site.json", root / "code-site.json")
    if axiom:
        add_axiom(root)
    shutil.rmtree(root / "forged")
    shutil.copy(PACKAGE_ROOT / "lean-toolchain", root / "lean-toolchain")
    subprocess.run(["lake", "build"], cwd=root, check=True)


@pytest.fixture(scope="session")
def replay_sites() -> dict[str, Path]:
    if shutil.which("lake") is None:
        pytest.skip("no `lake` to compile the fixture project")
    base = canonical_test_blueprint_output_dir("replay_site_fixture", Path(__file__))
    base.parent.mkdir(parents=True, exist_ok=True)
    honest, forged, assumed = base / "honest", base / "forged", base / "axiom"
    build_project(honest, forged=False)
    build_project(forged, forged=True)
    build_project(assumed, forged=False, axiom=True)
    sites = {}
    for state, root, flags in (("accepted", honest, []), ("rejected", forged, []),
                               ("none", honest, ["--no-kernel-replay"]), ("axiom", assumed, [])):
        out = base / f"site-{state}"
        if out.exists():
            shutil.rmtree(out)
        # through `lake env`, which names the toolchain whose `con-leche` and `con-ron` replay the
        # modules
        subprocess.run(
            ["lake", "env", str(vbp_executable()), "code-site", "--data", str(root / "code-site.json"),
             "--root", str(root), "--output", str(out), "--reproducible", *flags],
            cwd=root,
            check=True,
        )
        sites[state] = out / "html-multi"
    return sites


@pytest.fixture(scope="session")
def replay_urls(replay_sites: dict[str, Path]):
    procs, urls = [], {}
    for state, site in replay_sites.items():
        port = find_free_port()
        proc = subprocess.Popen(
            [sys.executable, "-m", "http.server", str(port), "--bind", "127.0.0.1"],
            cwd=site,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        urls[state] = f"http://127.0.0.1:{port}"
        wait_for_server(urls[state], proc)
        procs.append(proc)
    yield urls
    for proc in procs:
        proc.terminate()
        proc.wait()


def open_page(page: Page, url: str, scheme: str) -> None:
    page.emulate_media(color_scheme=scheme)
    page.goto(url, wait_until="load")


def wait_for_graph(page: Page) -> None:
    page.wait_for_function(
        """() => {
            const node = document.querySelector(".bp_graph_canvas svg g.node");
            const block = document.querySelector(".bp_graph_fullwidth");
            const state = block ? block.__bpGraphState : null;
            return !!node && !!state && state.renderFinalizedToken === state.renderToken;
        }""",
        timeout=60000,
    )


def computed(page: Page, selector: str, prop: str, pseudo: str | None = None) -> str:
    return page.evaluate(
        "([selector, prop, pseudo]) => getComputedStyle(document.querySelector(selector), pseudo)[prop]",
        [selector, prop, pseudo],
    )


def graph_nodes(page: Page) -> list[dict]:
    return page.evaluate(
        """() => Array.from(document.querySelectorAll(".bp_graph_canvas svg g.node")).map((g) => {
            const shape = g.querySelector(":scope > ellipse, :scope > path");
            return { cls: g.getAttribute("class"), fill: getComputedStyle(shape).fill,
                     stroke: getComputedStyle(shape).stroke };
        })"""
    )


@pytest.mark.parametrize("scheme", SCHEMES)
def test_accepted_site_draws_success_colours(page: Page, replay_urls: dict[str, str], scheme: str):
    base = replay_urls["accepted"]
    i = SCHEMES.index(scheme)
    open_page(page, base + "/Project-Stats/", scheme)
    assert page.locator(".bp_project_stats").get_attribute("data-bp-replay-state") == "accepted"
    assert "bp_replay_accepted" in page.locator(".bp_project_stats").get_attribute("class")
    assert page.locator(".bp_stats_verdict").inner_text() == "Lean statement proved"
    assert computed(page, ".bp_stats_verdict", "backgroundColor") == ACCEPTED_FILL[i]
    assert computed(page, ".bp_stats_bar .bp_stats_status_fully-proved", "backgroundColor") == ACCEPTED_FILL[i]
    assert computed(page, ".bp_stats_legend .bp_stats_status_fully-proved", "backgroundColor") == ACCEPTED_FILL[i]
    assert computed(page, ".bp_stats_replay_summary", "color", "::before") == ACCEPTED_BORDER[i]
    assert page.locator(".bp_stats_replay_counts").count() == 0
    legend = page.locator(".bp_stats_legend").inner_text()
    assert REPORTED_NOTE not in legend and REJECTED_NOTE not in legend

    open_page(page, base + "/Blueprint-Summary/", scheme)
    assert "bp_replay_accepted" in page.locator(".bp_summary").get_attribute("class")
    assert page.locator(".bp_summary_replay_note").count() == 0
    closed = page.locator(".bp_summary_card_status", has_text="Fully closed").first
    assert closed.evaluate("e => getComputedStyle(e).borderLeftColor") == ACCEPTED_FILL[i]

    open_page(page, base + "/Dependency-Graph/#node=Cmp.double_even", scheme)
    wait_for_graph(page)
    nodes = graph_nodes(page)
    assert nodes and all("bp_replay_accepted" in n["cls"] for n in nodes)
    assert all(n["fill"] == ACCEPTED_FILL[i] and n["stroke"] == ACCEPTED_BORDER[i] for n in nodes)
    assert "bp_replay_accepted" in page.locator(".bp_graph_legend").first.get_attribute("class")
    labels = page.locator(".bp_graph_legend[data-bp-legend-kind='full']").inner_text()
    assert "Lean code without sorry" in labels and REPORTED_NOTE not in labels
    page.wait_for_selector(".bp_graph_preview .bp_node_view .bp_status_glyph", timeout=60000)
    glyph = ".bp_graph_preview .bp_node_view .bp_status_glyph"
    assert page.locator(glyph).inner_text() == "✓"
    assert computed(page, glyph, "color") == ACCEPTED_BORDER[i]


@pytest.mark.parametrize("scheme", SCHEMES)
@pytest.mark.parametrize("state", ("rejected", "none"))
def test_without_an_accepted_replay_nothing_is_green(
        page: Page, replay_urls: dict[str, str], state: str, scheme: str):
    base = replay_urls[state]
    i = SCHEMES.index(scheme)
    note = REJECTED_NOTE if state == "rejected" else REPORTED_NOTE
    for path in PAGES:
        open_page(page, base + path, scheme)
        assert page.evaluate(GREEN_SCAN) == [], path

    open_page(page, base + "/Project-Stats/", scheme)
    assert page.locator(".bp_project_stats").get_attribute("data-bp-replay-state") == state
    assert f"bp_replay_{state}" in page.locator(".bp_project_stats").get_attribute("class")
    assert "proved" not in page.locator(".bp_stats_verdict").inner_text().lower()
    assert computed(page, ".bp_stats_bar .bp_stats_status_fully-proved", "backgroundColor") == REPORTED_FILL[i]
    assert computed(page, ".bp_stats_legend .bp_stats_status_fully-proved", "backgroundColor") == REPORTED_FILL[i]
    counts = page.locator(".bp_stats_replay_counts")
    legend = page.locator(".bp_stats_legend").inner_text()
    assert f"Lean complete, dependencies too ({note})" in legend
    if state == "rejected":
        assert "A kernel checker rejected this build" in counts.inner_text()
        # the headline and the sentence beside the counts are in the error colour
        for selector in (".bp_stats_replay_counts", ".bp_stats_replay_summary"):
            r, g, b = [int(v) for v in computed(page, selector, "color")[4:-1].split(", ")[:3]]
            assert r > g + 60 and r > b + 60, selector
        assert page.locator(".bp_stats_theorem").get_attribute("data-bp-verdict") == "rejected"
    else:
        assert "as the compiled files report, not replayed by a kernel" in counts.inner_text()

    open_page(page, base + "/Blueprint-Summary/", scheme)
    assert f"bp_replay_{state}" in page.locator(".bp_summary").get_attribute("class")
    assert page.locator(".bp_summary_replay_note").count() == 1
    closed = page.locator(".bp_summary_card_status", has_text="Fully closed").first
    assert closed.evaluate("e => getComputedStyle(e).borderLeftColor") == REPORTED_FILL[i]
    sentence = ("A kernel checker rejected this build." if state == "rejected"
                else "Counted as the compiled files report, not replayed by a kernel.")
    assert sentence in closed.inner_text()

    open_page(page, base + "/Dependency-Graph/#node=Cmp.double_even", scheme)
    wait_for_graph(page)
    nodes = graph_nodes(page)
    assert nodes and not any("bp_replay_accepted" in n["cls"] for n in nodes)
    assert all(n["fill"] == REPORTED_FILL[i] and n["stroke"] == REPORTED_BORDER[i] for n in nodes)
    labels = page.locator(".bp_graph_legend[data-bp-legend-kind='full']").inner_text()
    assert f"Lean code without sorry ({note})" in labels
    assert f"In Lean, no sorry ({note})" in labels
    page.wait_for_selector(".bp_graph_preview .bp_node_view .bp_status_glyph", timeout=60000)
    assert page.evaluate(GREEN_SCAN) == []
    glyph = page.locator(".bp_graph_preview .bp_node_view .bp_status_glyph")
    assert glyph.inner_text() == ("⊘" if state == "rejected" else "◇")


@pytest.mark.parametrize("scheme", SCHEMES)
def test_accepted_replay_with_an_axiom_says_so(page: Page, replay_urls: dict[str, str], scheme: str):
    base = replay_urls["axiom"]
    i = SCHEMES.index(scheme)
    open_page(page, base + "/Project-Stats/", scheme)
    assert page.locator(".bp_project_stats").get_attribute("data-bp-replay-state") == "none"
    # the replay band and the headline it covers stay positive
    assert page.locator(".bp_stats_replay_summary").inner_text().strip().startswith("Accepted: ")
    assert page.locator(".bp_stats_verdict").inner_text() == "Lean statement proved"
    # the counts are grey, and their words are true of this state
    assert computed(page, ".bp_stats_bar .bp_stats_status_fully-proved", "backgroundColor") == REPORTED_FILL[i]
    counts = page.locator(".bp_stats_replay_counts").inner_text()
    assert counts.startswith("The kernel replay accepted the build, and the counts are as the "
                             "compiled files report: "), counts
    # the node that rests on the axiom; the axiom's own node has a mark of its own and is not
    # counted as complete, so it is not one of them
    assert ": 1 node without sorry rests on the axiom Demo.assumed, so it was not checked" in counts, \
        counts
    legend = page.locator(".bp_stats_legend").inner_text()
    assert "(the kernel replay accepted the build; on this site " in legend, legend
    for text in (counts, legend):
        assert "not replayed" not in text and "no verdict" not in text, text

    open_page(page, base + "/Blueprint-Summary/", scheme)
    closed = page.locator(".bp_summary_card_status", has_text="Fully closed").first
    assert "Counted as the compiled files report: the kernel replay accepted the build" in closed.inner_text()
    assert "not replayed" not in page.locator(".bp_summary").inner_text()

    open_page(page, base + "/Dependency-Graph/#node=Demo.double_eq'", scheme)
    wait_for_graph(page)
    labels = page.locator(".bp_graph_legend[data-bp-legend-kind='full']").inner_text()
    assert "the kernel replay accepted the build" in labels and "not replayed" not in labels
    page.wait_for_selector(".bp_graph_preview .bp_node_view .bp_status_glyph", timeout=60000)
    glyph = page.locator(".bp_graph_preview .bp_node_view .bp_status_glyph")
    assert glyph.inner_text() == "⚠"
    title = glyph.get_attribute("title")
    assert "not checked by the kernel replay" in title and "Demo.assumed" in title, title
    assert "not shown as proved" in title, title


@pytest.mark.parametrize("scheme", SCHEMES)
@pytest.mark.parametrize("state", ("rejected", "none"))
def test_status_legend_sample_is_neutral_without_an_accepted_replay(
        page: Page, replay_urls: dict[str, str], state: str, scheme: str):
    """The status legend's sample check mark is about no node: on a page without an accepted
    replay behind it, it is drawn in the neutral colour, never green."""
    open_page(page, replay_urls[state] + "/Demo___Basic/", scheme)
    summary = page.locator(".bp_status_legend summary")
    if summary.count() == 0:
        pytest.skip("no status legend on this page")
    summary.first.click()
    colour = computed(page, ".bp_status_legend .bp_status_glyph_proved", "color")
    assert colour not in ACCEPTED_BORDER, colour



@pytest.mark.parametrize("state, words, never", [
    ("accepted", "checked again by con-leche and con-ron", ["not accepted", "not replayed"]),
    ("rejected", "not accepted: ", ["complete", "both accepted it"]),
    ("none", "as the compiled files report; not replayed by a kernel", ["complete", "accepted it"]),
])
def test_assistive_technology_gets_the_verdict(page: Page, replay_urls: dict[str, str], state: str,
                                               words: str, never: list[str]):
    # a node's accessible name and tooltip in the graph, and the Lean-code entry of its card,
    # say its state in the words of its mark, never "without sorry" alone
    base = replay_urls[state]
    open_page(page, base + "/Dependency-Graph/", "light")
    wait_for_graph(page)
    node = '.bp_graph_canvas svg g.node[data-bp-node-name="Cmp.double_even"][aria-label]'
    page.wait_for_selector(node, state="attached", timeout=60000)
    # the drawing's tooltip (`desc`) and the accessible name the page gives the node
    for text in (page.get_attribute(node, "aria-label"),
                 page.eval_on_selector(node, "g => (g.querySelector(':scope > desc') || {}).textContent || ''")):
        assert words in text, (state, text)
        assert not any(w in text for w in never), (state, text)
    open_page(page, base + "/Comparator___Double___Solution/", "light")
    labels = page.eval_on_selector_all(
        ".bp_code_summary_preview_wrap:has(> .bp_code_link_status), a.bp_code_link_status",
        "els => els.map(e => e.getAttribute('aria-label') || '')")
    assert labels, state
    for label in labels:
        assert words in label, (state, label)
        assert not any(w in label for w in never), (state, label)
