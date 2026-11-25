"""Browser checks that a page never shows a positive mark beside source text that is not known to
be the text that was compiled (manual, "Source text and the build").

* A site from compiled code: a copy of `comparator_site_fixture/`, built here with the toolchain's
  own `lake` and replayed by the kernel checkers; then the solution's file is edited and the site
  generated again without a build.
* A written Blueprint: the fork's own test Blueprint `lean-auto-deps`, whose nodes refer to
  declarations of `tests/VersoBlueprintTests/BlueprintAutoDeps/Preview.lean`, generated from a
  folder where that file is a copy, edited or not.

In both, every place that shows the edited module's declarations must say "changed since the
build", with no check mark, no "no sorry", no success colour; the other declarations keep theirs.

* A module the proof uses: the same fixture with the solution importing `Demo.Basic`, built, then
  `Demo.Basic`'s lemma turned into `sorry` before the site is generated (an edit between the
  build and the generation). The challenge's headline is not compared on every page that shows
  it, the solution's nodes, whose own source is unchanged, get the neutral mark naming the module
  that changed, and no count, legend or fill says complete.
"""

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest
from playwright.sync_api import Page

from conftest import REPLAY_RECORD_DIR, serve_site
from test_kernel_replay_colours import GREEN_SCAN
from scripts.blueprint_harness_paths import canonical_test_blueprint_output_dir
from support import PACKAGE_ROOT, lake_hash

FIXTURE = Path(__file__).parent / "comparator_site_fixture"
SOLUTION = Path("Comparator") / "Double" / "Solution.lean"
PREVIEW = Path("tests") / "VersoBlueprintTests" / "BlueprintAutoDeps" / "Preview.lean"
SUPPORT = Path("tests") / "VersoBlueprintTests" / "Blueprint" / "Support.lean"
BASIC = Path("Demo") / "Basic.lean"
IMPORTS = "imports Demo.Basic in Demo/Basic.lean, which changed since the build"
NOT_COMPARED = ("Not compared: a module the proof uses changed since the build "
                "(Demo.Basic in Demo/Basic.lean); build it again after an edit.")
EDIT = "\n-- edited after the build\n"


def vbp_executable() -> Path:
    exe = PACKAGE_ROOT / ".lake" / "build" / "bin" / "vbp"
    if not exe.exists():
        subprocess.run(["lake", "build", "vbp"], cwd=PACKAGE_ROOT, check=True)
    return exe


def docs_executable() -> Path:
    exe = PACKAGE_ROOT / ".lake" / "build" / "bin" / "blueprint-test-docs"
    if not exe.exists():
        subprocess.run(["lake", "build", "blueprint-test-docs"], cwd=PACKAGE_ROOT, check=True)
    return exe


@pytest.fixture(scope="session")
def code_sites() -> dict[str, Path]:
    """The comparator fixture built by Lake, its site as built, and after an edit of the solution
    without a build: the Lake build record of the solution before the edit, too."""
    if shutil.which("lake") is None:
        pytest.skip("no `lake` to compile the fixture project")
    base = canonical_test_blueprint_output_dir("source_provenance", Path(__file__))
    base.parent.mkdir(parents=True, exist_ok=True)
    root = base / "project"
    if root.exists():
        shutil.rmtree(root)
    shutil.copytree(FIXTURE, root)
    shutil.rmtree(root / "forged")
    shutil.copy(PACKAGE_ROOT / "lean-toolchain", root / "lean-toolchain")
    subprocess.run(["lake", "build"], cwd=root, check=True)
    sites = {}
    trace = root / ".lake" / "build" / "lib" / "lean" / "Comparator" / "Double" / "Solution.trace"
    for state in ("built", "untraced", "edited"):
        if state == "untraced":
            # no build record says which source the solution was compiled from
            trace.rename(trace.with_suffix(".trace-aside"))
        if state == "edited":
            trace.with_suffix(".trace-aside").rename(trace)
            text = (root / SOLUTION).read_text(encoding="utf-8")
            (root / SOLUTION).write_text(
                text.replace("unfold double; omega", "sorry -- edited after the build"),
                encoding="utf-8")
        out = base / f"site-{state}"
        if out.exists():
            shutil.rmtree(out)
        result = subprocess.run(
            ["lake", "env", str(vbp_executable()), "code-site", "--data",
             str(root / "code-site.json"), "--root", str(root), "--output", str(out),
             "--reproducible"],
            cwd=root, capture_output=True, text=True)
        assert result.returncode == 0, result.stderr
        sites[state] = out / "html-multi"
        sites[f"{state}-log"] = result.stderr
    sites["root"] = root
    return sites


@pytest.fixture(scope="session")
def written_sites(tmp_path_factory) -> dict[str, Path]:
    """The test Blueprint `lean-auto-deps` generated from a folder with a copy of the sources of
    the module its nodes refer to and of the project modules it imports, as built, with that
    module edited, and with a module it imports edited."""
    exe = docs_executable()
    sites = {}
    for state in ("built", "edited", "imported"):
        root = tmp_path_factory.mktemp(f"written-{state}")
        for tree in ("src", Path("tests") / "VersoBlueprintTests"):
            shutil.copytree(PACKAGE_ROOT / tree, root / tree,
                            ignore=shutil.ignore_patterns("*.olean", ".lake"))
        if state == "edited":
            (root / PREVIEW).write_text(
                (root / PREVIEW).read_text(encoding="utf-8") + EDIT, encoding="utf-8")
        if state == "imported":
            (root / SUPPORT).write_text(
                (root / SUPPORT).read_text(encoding="utf-8") + EDIT, encoding="utf-8")
        shutil.copy(PACKAGE_ROOT / "lean-toolchain", root / "lean-toolchain")
        out = root / "_out"
        result = subprocess.run([str(exe), "lean-auto-deps", "--output", str(out)], cwd=root,
                                capture_output=True, text=True)
        assert result.returncode == 0, result.stderr
        sites[state] = out / "html-multi"
    return sites


def graph_nodes(page: Page, url: str) -> list[dict]:
    page.goto(f"{url}/Dependency-Graph/")
    page.wait_for_selector(".bp_graph_canvas svg g.node")
    return page.evaluate(
        """() => [...document.querySelectorAll('.bp_graph_canvas svg g.node')].map(n => ({
            name: n.getAttribute('data-bp-node-name') || '',
            classes: n.getAttribute('class') || '',
            label: n.getAttribute('aria-label') || '',
            fill: getComputedStyle(n.querySelector('ellipse, path')).fill
        }))""")


def test_replay_record_is_scratch(code_sites: dict[str, Path]):
    # the accepted replay of the fixture recorded its acceptance in the suite's scratch folder,
    # not in the user's cache
    record = Path(os.environ["VERSO_BLUEPRINT_KERNEL_REPLAY_RECORD"])
    assert record.parent == REPLAY_RECORD_DIR
    assert record.is_file()


def published_files_naming(site: Path, roots: list[str]) -> list[str]:
    """The files of the site whose text names one of `roots`."""
    found = []
    for f in site.rglob("*"):
        if f.is_file():
            text = f.read_bytes()
            if any(root.encode() in text for root in roots):
                found.append(str(f.relative_to(site)))
    return found


def test_published_files_name_no_path_of_the_build_machine(code_sites, written_sites):
    # paths are relative to the project root, in the pages, the manifest, the cross-reference
    # data and the search data alike
    root = code_sites["root"]
    roots = [str(root), str(root.resolve()), str(PACKAGE_ROOT), str(PACKAGE_ROOT.resolve())]
    for name in ("built", "edited"):
        assert published_files_naming(code_sites[name], roots) == [], name
        assert published_files_naming(written_sites[name], roots) == [], name
    assert published_files_naming(code_sites["untraced"], roots) == []


def test_lake_hash_is_lakes(code_sites: dict[str, Path]):
    # the helper that writes stand-in build records hashes as Lake does
    root = code_sites["root"]
    trace = json.loads((root / ".lake" / "build" / "lib" / "lean" / "Comparator" / "Double" /
                        "Solution.trace").read_text(encoding="utf-8"))
    olean = root / ".lake" / "build" / "lib" / "lean" / "Comparator" / "Double" / "Solution.olean"
    assert f"{lake_hash(olean.read_bytes())}.olean" in trace["outputs"]["o"]


def test_code_site_edited_after_the_build(page: Page, code_sites: dict[str, Path]):
    with serve_site(code_sites["edited"]) as url:
        page.goto(f"{url}/Comparator___Double___Solution/")
        text = page.locator("main").text_content()
        assert "sorry -- edited after the build" in text
        assert "changed since the build" in text
        assert "[no sorry]" not in text
        assert "✓" not in page.locator(".bp_status_glyph").all_inner_texts()
        # the Lean-code entry of each node, as assistive technology names it
        labels = page.eval_on_selector_all(
            ".bp_code_summary_preview_wrap:has(> .bp_code_link_status), a.bp_code_link_status",
            "els => els.map(e => e.getAttribute('aria-label') || '')")
        assert labels and all("changed since the build" in label for label in labels), labels
        nodes = {n["name"]: n for n in graph_nodes(page, url)}
        edited = nodes["Cmp.double_even"]
        assert "bp_graph_status_source_changed" in edited["classes"]
        assert "bp_replay_accepted" not in edited["classes"]
        assert "changed since the build" in edited["label"], edited
        # the other module's declarations keep the replay's verdict
        assert "bp_replay_accepted" in nodes["Demo.double"]["classes"]
        assert "checked again by con-leche and con-ron" in nodes["Demo.double"]["label"]
        page.goto(f"{url}/Project-Stats/")
        band = page.locator(".bp_stats_replay_source_changed").inner_text()
        assert "Comparator.Double.Solution" in band and "changed since the build" in band
        assert page.locator('.bp_stats_bar [data-bp-status="source-changed"]').count() >= 1


def test_code_site_as_built_keeps_its_marks(page: Page, code_sites: dict[str, Path]):
    with serve_site(code_sites["built"]) as url:
        nodes = {n["name"]: n for n in graph_nodes(page, url)}
        assert "bp_replay_accepted" in nodes["Cmp.double_even"]["classes"]
        assert not any("source_changed" in n["classes"] for n in nodes.values())
        page.goto(f"{url}/Project-Stats/")
        assert page.locator(".bp_stats_replay_source_changed").count() == 0


def test_written_blueprint_edited_after_the_build(page: Page, written_sites: dict[str, Path]):
    with serve_site(written_sites["edited"]) as url:
        nodes = graph_nodes(page, url)
        changed = [n for n in nodes if "source_changed" in n["classes"]]
        assert changed, nodes
        for node in changed:
            assert "changed since the build" in node["label"], node
        page.goto(f"{url}/")
        badges = page.locator(".bp_external_decl_header_status").all_inner_texts()
        assert badges and "no sorry" not in badges, badges
        assert all(b == "source changed since the build" for b in badges), badges


def test_written_blueprint_on_an_edited_import(page: Page, written_sites: dict[str, Path]):
    # the nodes' own module is as built; a project module it imports is not: no node keeps a
    # positive mark, and each names the module that changed
    with serve_site(written_sites["imported"]) as url:
        nodes = graph_nodes(page, url)
        changed = [n for n in nodes if "source_changed" in n["classes"]]
        assert changed, nodes
        for node in changed:
            assert ("imports VersoBlueprintTests.Blueprint.Support in "
                    f"{SUPPORT.as_posix()}, which changed since the build") in node["label"], node
        assert not any("bp_replay_accepted" in n["classes"] for n in nodes)
        # a node whose Lean is a code block of the Blueprint itself too
        assert not any("bp_graph_status_formalized" in n["classes"] for n in nodes), nodes
        inline = next(n for n in nodes if "auto.demo.inline_target" in n["label"])
        assert "source_changed" in inline["classes"], inline
        page.goto(f"{url}/Project-Stats/")
        band = page.locator(".bp_stats_replay_source_changed").inner_text()
        assert "the source of VersoBlueprintTests.Blueprint.Support" in band, band


def test_written_blueprint_as_built_keeps_its_marks(page: Page, written_sites: dict[str, Path]):
    with serve_site(written_sites["built"]) as url:
        nodes = graph_nodes(page, url)
        assert not any("source_changed" in n["classes"] for n in nodes), nodes


@pytest.fixture(scope="session")
def import_sites() -> dict[str, Path]:
    """The comparator fixture with the solution importing `Demo.Basic`, built by Lake, its site as
    built, and after `Demo.Basic`'s lemma was turned into `sorry` without a build."""
    if shutil.which("lake") is None:
        pytest.skip("no `lake` to compile the fixture project")
    base = canonical_test_blueprint_output_dir("source_imports", Path(__file__))
    base.parent.mkdir(parents=True, exist_ok=True)
    root = base / "project"
    if root.exists():
        shutil.rmtree(root)
    shutil.copytree(FIXTURE, root)
    shutil.rmtree(root / "forged")
    shutil.copy(PACKAGE_ROOT / "lean-toolchain", root / "lean-toolchain")
    # the import takes the place of the first line, so the data's source ranges still hold
    lines = (root / SOLUTION).read_text(encoding="utf-8").split("\n")
    (root / SOLUTION).write_text("\n".join(["import Demo.Basic"] + lines[1:]), encoding="utf-8")
    subprocess.run(["lake", "build"], cwd=root, check=True)
    sites = {}
    for state in ("built", "edited"):
        if state == "edited":
            text = (root / BASIC).read_text(encoding="utf-8")
            (root / BASIC).write_text(
                text.replace("unfold double; omega", "sorry -- edited after the build", 1),
                encoding="utf-8")
        out = base / f"site-{state}"
        if out.exists():
            shutil.rmtree(out)
        result = subprocess.run(
            ["lake", "env", str(vbp_executable()), "code-site", "--data",
             str(root / "code-site.json"), "--root", str(root), "--output", str(out),
             "--reproducible"],
            cwd=root, capture_output=True, text=True)
        assert result.returncode == 0, result.stderr
        sites[state] = out / "html-multi"
        sites[f"{state}-log"] = result.stderr
    return sites



def double_verdicts(page: Page, scope: str) -> list[tuple[str, str]]:
    """The verdict token and words of each judged theorem of the challenge `Double` in `scope`."""
    return page.evaluate(
        """(scope) => Array.from(document.querySelectorAll(
              scope + ' [data-bp-challenge="Double"] [data-bp-theorem], '
              + scope + '[data-bp-challenge="Double"] [data-bp-theorem]'))
            .map((e) => [e.getAttribute("data-bp-verdict") || "",
                         e.textContent || ""])""",
        scope)


def test_proof_on_an_edited_module_is_not_proved(page: Page, import_sites: dict[str, Path]):
    with serve_site(import_sites["edited"]) as url:
        # the headline, on the stats page, the challenge index and the challenge's own page
        for path, scope in (("/Project-Stats/", ".bp_project_stats"),
                            ("/Comparator/", ".bp_comparator_index"),
                            ("/Comparator/Double/", "main")):
            page.goto(f"{url}{path}")
            text = page.locator("main").inner_text()
            assert NOT_COMPARED in text, path
            found = double_verdicts(page, scope)
            # the index lists the reason alone; the other two pages the theorem as not compared
            assert found or path == "/Comparator/", path
            for token, words in found:
                assert token not in ("proved", "not-replayed"), (path, token)
                assert "proved" not in words.lower() and "✓" not in words, (path, words)
            assert page.locator('[data-bp-challenge="Double"] .bp_stats_verdict_proved').count() == 0
        # the solution's node: its own source is as built, the module it imports is not
        nodes = {n["name"]: n for n in graph_nodes(page, url)}
        solution = nodes["Cmp.double_even"]
        assert "bp_graph_status_source_changed" in solution["classes"], solution
        assert "bp_replay_accepted" not in solution["classes"]
        assert IMPORTS in solution["label"], solution
        assert not any("bp_replay_accepted" in n["classes"] for n in nodes.values())
        tooltip = page.eval_on_selector(
            'g.node[data-bp-node-name="Cmp.double_even"] desc', "e => e.textContent")
        assert IMPORTS in tooltip and "complete:" not in tooltip, tooltip
        legend = page.locator(".bp_graph_legend").first.inner_text()
        assert "a project module it imports" in legend, legend
        # the chapter of the solution: no check mark, the Lean-code entry names the module
        page.goto(f"{url}/Comparator___Double___Solution/")
        assert "✓" not in page.locator(".bp_status_glyph").all_inner_texts()
        labels = page.eval_on_selector_all(
            ".bp_code_summary_preview_wrap:has(> .bp_code_link_status), a.bp_code_link_status",
            "els => els.map(e => e.getAttribute('aria-label') || '')")
        assert labels and all(IMPORTS in label for label in labels), labels
        # the counts: nothing counted as complete, every node in the neutral bucket
        page.goto(f"{url}/Project-Stats/")
        statuses = page.eval_on_selector_all(
            ".bp_stats_bar [data-bp-status]", "els => els.map(e => e.dataset.bpStatus)")
        assert statuses and set(statuses) == {"source-changed"}, statuses
        band = page.locator(".bp_stats_replay_source_changed").inner_text()
        assert "Comparator.Double.Solution" in band and IMPORTS in band, band


def test_proof_on_the_modules_as_built_is_proved(page: Page, import_sites: dict[str, Path]):
    with serve_site(import_sites["built"]) as url:
        page.goto(f"{url}/Project-Stats/")
        found = double_verdicts(page, ".bp_project_stats")
        assert [token for token, _ in found] == ["proved"], found
        assert page.locator(".bp_stats_replay_source_changed").count() == 0
        nodes = {n["name"]: n for n in graph_nodes(page, url)}
        assert "bp_replay_accepted" in nodes["Cmp.double_even"]["classes"]
        assert not any("source_changed" in n["classes"] for n in nodes.values())



# The replay band beside sources that are not the build's text: "Accepted" only for the compiled
# build, the neutral mark, no check mark, nothing green; the generator's last line agrees.
SOLUTION_PLACE = "Comparator.Double.Solution in Comparator/Double/Solution.lean"
BASIC_PLACE = "Demo.Basic in Demo/Basic.lean"
ON_CHANGED = "Accepted for the compiled build, not for the sources shown: "
ON_UNKNOWN = "Accepted for the compiled build, which is not known to match the sources shown: "


def replay_band(page: Page) -> dict:
    """The replay band's first sentence: its classes, attributes, text and mark, and the band's
    whole text."""
    return page.evaluate(
        """() => {
            const e = document.querySelector(".bp_stats_replay_summary");
            const before = getComputedStyle(e, "::before");
            return { cls: e.getAttribute("class"), replay: e.getAttribute("data-bp-replay"),
                     sources: e.getAttribute("data-bp-replay-sources"), text: e.textContent,
                     mark: before.content, band: document.querySelector(".bp_stats_replay").textContent };
        }""")


def last_replay_line(log: str) -> str:
    return [line for line in log.splitlines() if line.startswith("Kernel replay: ")][-1]


def band_green(page: Page) -> list[str]:
    """The greenish colours inside the replay band."""
    scan = GREEN_SCAN.replace('querySelectorAll("body *")',
                              'querySelectorAll(".bp_stats_replay, .bp_stats_replay *")')
    assert scan != GREEN_SCAN
    return page.evaluate(scan)


@pytest.mark.parametrize("scheme", ("light", "dark"))
def test_replay_band_beside_an_edited_solution(page: Page, code_sites: dict[str, Path],
                                               scheme: str):
    page.emulate_media(color_scheme=scheme)
    with serve_site(code_sites["edited"]) as url:
        page.goto(f"{url}/Project-Stats/")
        band = replay_band(page)
        assert band["replay"] == "changed" and band["sources"] == "changed", band
        assert "bp_stats_replay_changed" in band["cls"] and "bp_replay_none" in band["cls"]
        assert "accepted" not in band["cls"], band
        assert "◌" in band["mark"], band
        assert "✓" not in band["mark"] and "✓" not in band["band"], band
        assert band["text"].startswith(ON_CHANGED), band
        assert f"The sources changed since that build ({SOLUTION_PLACE}" in band["text"], band
        assert band["text"].endswith("; build it again after an edit."), band
        assert "Declarations checked in the compiled build" in band["band"]
        assert band_green(page) == []
    line = last_replay_line(code_sites["edited-log"])
    assert line.startswith("Kernel replay: both checkers accepted the compiled build ("), line
    assert "not the sources: they changed since that build" in line and SOLUTION_PLACE in line


def test_replay_band_beside_an_edited_import(page: Page, import_sites: dict[str, Path]):
    # the solution's own source is as built; a module it imports is not
    with serve_site(import_sites["edited"]) as url:
        page.goto(f"{url}/Project-Stats/")
        band = replay_band(page)
        assert band["replay"] == "changed" and band["sources"] == "changed", band
        assert "accepted" not in band["cls"], band
        assert "✓" not in band["mark"] and "✓" not in band["band"], band
        assert band["text"].startswith(ON_CHANGED), band
        assert f"The sources changed since that build ({BASIC_PLACE}" in band["text"], band
        # the importing module is not named as changed: its own source is as built
        assert SOLUTION_PLACE not in band["text"], band
        assert band_green(page) == []
    assert "not the sources" in last_replay_line(import_sites["edited-log"])


@pytest.mark.parametrize("scheme", ("light", "dark"))
def test_replay_band_beside_a_source_not_known_to_match(page: Page, code_sites: dict[str, Path],
                                                        scheme: str):
    page.emulate_media(color_scheme=scheme)
    with serve_site(code_sites["untraced"]) as url:
        page.goto(f"{url}/Project-Stats/")
        band = replay_band(page)
        assert band["replay"] == "changed" and band["sources"] == "unknown", band
        assert "bp_stats_replay_changed" in band["cls"] and "accepted" not in band["cls"], band
        assert "◌" in band["mark"], band
        assert "✓" not in band["mark"] and "✓" not in band["band"], band
        assert band["text"].startswith(ON_UNKNOWN), band
        assert ("The sources shown are not known to be the text that was compiled "
                f"({SOLUTION_PLACE}, which is not known to match the build: ") in band["text"], band
        assert band["text"].endswith("; build it again to compare them."), band
        assert band_green(page) == []
        # the headline says the same of the challenge
        assert "Not compared: a module the proof uses is not known to match the build" in \
            page.locator("main").inner_text()
    line = last_replay_line(code_sites["untraced-log"])
    assert "the sources are not known to match it" in line and SOLUTION_PLACE in line, line


@pytest.mark.parametrize("which", ("code", "import"))
def test_replay_band_on_sources_as_built(page: Page, code_sites: dict[str, Path],
                                         import_sites: dict[str, Path], which: str):
    site = code_sites if which == "code" else import_sites
    with serve_site(site["built"]) as url:
        page.goto(f"{url}/Project-Stats/")
        band = replay_band(page)
        assert band["cls"] == ("bp_stats_lead bp_stats_replay_summary bp_stats_replay_accepted "
                               "bp_replay_accepted"), band
        assert band["replay"] == "accepted" and band["sources"] is None, band
        assert band["text"].startswith("Accepted: con-leche and con-ron"), band
        assert "✓" in band["mark"], band
        assert "compiled build" not in band["band"]
    assert last_replay_line(site["built-log"]).startswith(
        "Kernel replay: accepted by both checkers, ")
