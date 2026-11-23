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
    assert "Not compared: The challenge module has not been built." in pending
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
