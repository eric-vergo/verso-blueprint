"""Browser checks that the Blueprint style switcher never covers the page's text.

On a site without the Blueprint sidebar the switcher sits in the foot of the table of contents,
in the page's layout; a box floating over the bottom corner of the window would cover whatever
text scrolls under it (the method sentence under a headline card, say). The site with the
sidebar is covered by `test_sidebar_runtime.py`.
"""

import pytest
from playwright.sync_api import Page, expect

SITE = "blueprint-grafts"

# The text elements of the page body whose boxes meet the switcher's box.
COVERED = """() => {
    const sw = document.getElementById("bp-style-switcher");
    const a = sw.getBoundingClientRect();
    const covered = [];
    for (const e of document.querySelectorAll("main *")) {
        if (e.children.length || !e.textContent.trim()) continue;
        const b = e.getBoundingClientRect();
        if (b.width && a.left < b.right && b.left < a.right && a.top < b.bottom && b.top < a.bottom) {
            covered.push(e.tagName + ": " + e.textContent.trim().slice(0, 40));
        }
    }
    return covered;
}"""


@pytest.mark.parametrize("scheme", ("light", "dark"))
@pytest.mark.parametrize("width", (390, 1280, 1500))
def test_switcher_without_sidebar_covers_no_text(page: Page, named_site, width: int, scheme: str):
    base = named_site(SITE)
    page.set_viewport_size({"width": width, "height": 900})
    page.emulate_media(color_scheme=scheme)
    page.goto(base + "/Project-Stats/", wait_until="load")
    switcher = page.locator("#toc > .last > #bp-style-switcher")
    expect(switcher).to_have_count(1)
    assert switcher.evaluate("e => getComputedStyle(e).position") == "static"
    for scroll in (0, 400, 800):
        page.evaluate("y => window.scrollTo(0, y)", scroll)
        assert page.evaluate(COVERED) == [], (width, scheme, scroll)
    if width >= 1280:
        expect(switcher).to_be_visible()
        expect(switcher.locator("select")).to_be_enabled()
