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
from scripts.blueprint_harness_paths import canonical_test_blueprint_output_dir
from support import PACKAGE_ROOT, lake_hash

FIXTURE = Path(__file__).parent / "comparator_site_fixture"
SOLUTION = Path("Comparator") / "Double" / "Solution.lean"
PREVIEW = Path("tests") / "VersoBlueprintTests" / "BlueprintAutoDeps" / "Preview.lean"
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
    for state in ("built", "edited"):
        if state == "edited":
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
    sites["root"] = root
    return sites


@pytest.fixture(scope="session")
def written_sites(tmp_path_factory) -> dict[str, Path]:
    """The test Blueprint `lean-auto-deps` generated from a folder with a copy of the module its
    nodes refer to, as built and edited."""
    exe = docs_executable()
    sites = {}
    for state in ("built", "edited"):
        root = tmp_path_factory.mktemp(f"written-{state}")
        (root / PREVIEW).parent.mkdir(parents=True)
        text = (PACKAGE_ROOT / PREVIEW).read_text(encoding="utf-8")
        (root / PREVIEW).write_text(text + (EDIT if state == "edited" else ""), encoding="utf-8")
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


def test_written_blueprint_as_built_keeps_its_marks(page: Page, written_sites: dict[str, Path]):
    with serve_site(written_sites["built"]) as url:
        nodes = graph_nodes(page, url)
        assert not any("source_changed" in n["classes"] for n in nodes), nodes
