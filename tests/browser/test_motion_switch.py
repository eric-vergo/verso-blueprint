"""Browser checks for the animations switch and the motion hook classes (`Informal.Motion`).

The showcase's "Animated Figures" chapter holds one script-free animated SVG (a dot turning about a
centre, once every four seconds) wrapped in the hook classes, with a still picture beside it.
"""

import pytest
from playwright.sync_api import Page, expect

from support import assert_no_runtime_errors, record_runtime_errors

MOTION_PAGE = "/Animated-Figures/"
STILL_PAGE = "/Reading-Aids/"
STORAGE_KEY = "verso-blueprint-motion"
LOOP_SECONDS = 4.0

# The dot's angle about the centre as drawn, and the figure's animation clock, read in the same
# frame.
READING_JS = """() => new Promise((resolve) => requestAnimationFrame(() => {
  const svg = document.getElementById('bp-motion-demo-svg');
  const dot = document.getElementById('bp-motion-demo-dot').getBoundingClientRect();
  const box = svg.getBoundingClientRect();
  const dx = dot.left + dot.width / 2 - (box.left + box.width / 2);
  const dy = dot.top + dot.height / 2 - (box.top + box.height / 2);
  resolve({ time: svg.getCurrentTime(), angle: (Math.atan2(dy, dx) * 180 / Math.PI + 360) % 360 });
}))"""

# Records the computed visibility of the live figure the moment the parser inserts it, before the
# page can be drawn with it.
FIRST_SIGHT_PROBE = """
window.__bpMotionFirstSight = [];
new MutationObserver((records) => {
  for (const record of records) {
    for (const node of record.addedNodes) {
      if (node.nodeType === 1 && node.matches('.bp_motion_live')) {
        window.__bpMotionFirstSight.push(getComputedStyle(node).visibility);
      }
    }
  }
}).observe(document, { childList: true, subtree: true });
"""

BLOCK_STORAGE = """
Object.defineProperty(window, 'localStorage', {
  configurable: true,
  get() { throw new DOMException('The storage is blocked.', 'SecurityError'); },
});
"""

# Contrast of an element's text against what is drawn behind it (its ancestors' backgrounds,
# composed), as WCAG computes it.
CONTRAST_JS = """(el) => {
  const parse = (c) => { const p = (c.match(/[\\d.]+/g) || [0, 0, 0, 0]).map(Number); return { r: p[0], g: p[1], b: p[2], a: p.length > 3 ? p[3] : 1 }; };
  const over = (top, under) => ({ r: top.r * top.a + under.r * (1 - top.a), g: top.g * top.a + under.g * (1 - top.a), b: top.b * top.a + under.b * (1 - top.a), a: 1 });
  const layers = [];
  for (let node = el; node; node = node.parentElement) {
    const bg = parse(getComputedStyle(node).backgroundColor);
    if (bg.a > 0) layers.push(bg);
    if (bg.a >= 1) break;
  }
  let bg = { r: 255, g: 255, b: 255, a: 1 };
  for (let i = layers.length - 1; i >= 0; i--) bg = over(layers[i], bg);
  const fg = over(parse(getComputedStyle(el).color), bg);
  const lum = (c) => { const f = (v) => { v /= 255; return v <= 0.03928 ? v / 12.92 : Math.pow((v + 0.055) / 1.055, 2.4); }; return 0.2126 * f(c.r) + 0.7152 * f(c.g) + 0.0722 * f(c.b); };
  const [x, y] = [lum(fg), lum(bg)].sort((p, q) => q - p);
  return (x + 0.05) / (y + 0.05);
}"""


def reading(page: Page) -> dict:
    return page.evaluate(READING_JS)


def angle_gap(a: float, b: float) -> float:
    d = abs(a - b) % 360
    return min(d, 360 - d)


def assert_follows_clock(r: dict) -> None:
    """The dot is where the animation's clock puts it (it starts at angle 0, turning clockwise on
    the screen)."""
    expected = (r["time"] % LOOP_SECONDS) / LOOP_SECONDS * 360
    assert angle_gap(r["angle"], expected) < 15, (r, expected)


def control(page: Page):
    return page.locator(".bp_motion_toggle")


def choice(page: Page, which: str):
    return page.locator(f'.bp_motion_toggle [data-motion-choice="{which}"]')


def live(page: Page):
    return page.locator("#bp-motion-demo .bp_motion_live")


def stills(page: Page):
    return page.locator("#bp-motion-demo .bp_motion_stills")


def computed(locator, prop: str) -> str:
    return locator.evaluate(f"e => getComputedStyle(e).{prop}")


@pytest.fixture
def motion_page(server: str, page: Page):
    """The page with the animated figure, with no stored choice and the system not asking for
    reduced motion."""
    page.emulate_media(reduced_motion="no-preference")
    page.goto(server + MOTION_PAGE)
    page.evaluate(f"localStorage.removeItem('{STORAGE_KEY}')")
    page.reload()
    expect(control(page)).to_be_visible()
    return page


class TestMotionSwitch:
    def test_switch_only_on_pages_with_motion(self, server: str, page: Page):
        errors = record_runtime_errors(page)
        page.emulate_media(reduced_motion="no-preference")
        page.goto(server + MOTION_PAGE)
        expect(control(page)).to_be_visible()
        expect(control(page)).to_have_attribute("role", "radiogroup")
        expect(control(page)).to_have_accessible_name("Animations")
        # right after the theme control, in the foot of the table of contents
        follows_theme = page.evaluate(
            "() => document.querySelector('[data-verso-theme-toggle]').nextElementSibling"
            ".classList.contains('bp_motion')"
        )
        assert follows_theme
        for path in ("/", STILL_PAGE):
            page.goto(server + path)
            expect(page.locator("[data-verso-theme-toggle]")).to_be_visible()
            expect(page.locator(".bp_motion")).to_have_count(0)
        assert_no_runtime_errors(errors)

    def test_motion_on_by_default_and_the_figure_moves(self, motion_page: Page):
        page = motion_page
        errors = record_runtime_errors(page)
        expect(choice(page, "on")).to_have_attribute("aria-checked", "true")
        expect(choice(page, "off")).to_have_attribute("aria-checked", "false")
        assert page.evaluate("document.documentElement.getAttribute('data-motion')") is None
        assert computed(live(page), "visibility") == "visible"
        assert computed(stills(page), "display") == "none"
        first = reading(page)
        page.wait_for_timeout(700)
        second = reading(page)
        assert second["time"] > first["time"]
        assert_follows_clock(first)
        assert_follows_clock(second)
        assert angle_gap(first["angle"], second["angle"]) > 10, (first, second)
        assert_no_runtime_errors(errors)

    def test_turning_motion_off_shows_the_still_picture(self, motion_page: Page):
        page = motion_page
        errors = record_runtime_errors(page)
        choice(page, "off").click()
        expect(page.locator("html")).to_have_attribute("data-motion", "reduce")
        expect(choice(page, "off")).to_have_attribute("aria-checked", "true")
        expect(choice(page, "on")).to_have_attribute("aria-checked", "false")
        assert page.evaluate(f"localStorage.getItem('{STORAGE_KEY}')") == "reduce"
        assert computed(live(page), "visibility") == "hidden"
        assert computed(live(page), "position") == "absolute"
        assert computed(live(page), "pointerEvents") == "none"
        assert computed(stills(page), "display") == "block"
        expect(stills(page)).to_be_visible()
        expect(live(page).locator("svg")).not_to_be_visible()
        choice(page, "on").click()
        assert page.evaluate("document.documentElement.getAttribute('data-motion')") is None
        assert page.evaluate(f"localStorage.getItem('{STORAGE_KEY}')") is None
        assert computed(live(page), "visibility") == "visible"
        assert computed(stills(page), "display") == "none"
        assert_no_runtime_errors(errors)

    def test_animation_follows_its_clock_after_off_and_on(self, motion_page: Page):
        # Hiding a running SVG animation must not leave it stopped when it is shown again.
        page = motion_page
        choice(page, "off").click()
        before = page.evaluate("document.getElementById('bp-motion-demo-svg').getCurrentTime()")
        page.wait_for_timeout(1500)
        choice(page, "on").click()
        first = reading(page)
        assert first["time"] > before + 0.5
        page.wait_for_timeout(600)
        second = reading(page)
        assert_follows_clock(first)
        assert_follows_clock(second)
        assert angle_gap(first["angle"], second["angle"]) > 10, (first, second)
        # and the picture on the screen changes with it
        figure = live(page).locator("svg")
        shot = figure.screenshot()
        page.wait_for_timeout(500)
        assert figure.screenshot() != shot

    def test_choice_survives_navigation_and_reload(self, motion_page: Page, server: str):
        page = motion_page
        choice(page, "off").click()
        page.goto(server + STILL_PAGE)
        # applied on a page without motion too, and still no switch there
        expect(page.locator("html")).to_have_attribute("data-motion", "reduce")
        expect(page.locator(".bp_motion")).to_have_count(0)
        page.goto(server + MOTION_PAGE)
        expect(choice(page, "off")).to_have_attribute("aria-checked", "true")
        assert computed(live(page), "visibility") == "hidden"
        page.reload()
        expect(page.locator("html")).to_have_attribute("data-motion", "reduce")
        expect(choice(page, "off")).to_have_attribute("aria-checked", "true")

    def test_figure_never_shows_moving_when_motion_is_off(self, motion_page: Page, server: str):
        page = motion_page
        choice(page, "off").click()
        page.add_init_script(FIRST_SIGHT_PROBE)
        page.goto(server + MOTION_PAGE)
        assert page.evaluate("window.__bpMotionFirstSight") == ["hidden"]
        page.reload()
        assert page.evaluate("window.__bpMotionFirstSight") == ["hidden"]
        choice(page, "on").click()
        page.reload()
        assert page.evaluate("window.__bpMotionFirstSight") == ["visible"]

    def test_system_reduced_motion(self, server: str, page: Page):
        errors = record_runtime_errors(page)
        page.emulate_media(reduced_motion="reduce")
        page.goto(server + MOTION_PAGE)
        page.evaluate(f"localStorage.removeItem('{STORAGE_KEY}')")
        page.reload()
        # nothing moves, without a stored choice
        assert computed(live(page), "visibility") == "hidden"
        assert computed(stills(page), "display") == "block"
        # the switch shows it off, and cannot turn it on; a note says why
        off, on = choice(page, "off"), choice(page, "on")
        expect(off).to_have_attribute("aria-checked", "true")
        expect(on).to_have_attribute("aria-checked", "false")
        expect(on).to_have_attribute("aria-disabled", "true")
        note = page.locator(".bp_motion_note")
        expect(note).to_be_visible()
        expect(note).to_contain_text("reduced motion")
        expect(control(page)).to_have_accessible_description(note.text_content())
        on.click(force=True)
        assert computed(live(page), "visibility") == "hidden"
        expect(on).to_have_attribute("aria-checked", "false")
        assert page.evaluate(f"localStorage.getItem('{STORAGE_KEY}')") is None
        # the system setting changes while the page is open
        page.emulate_media(reduced_motion="no-preference")
        expect(on).to_have_attribute("aria-checked", "true")
        expect(on).not_to_have_attribute("aria-disabled", "true")
        expect(note).to_be_hidden()
        assert computed(live(page), "visibility") == "visible"
        assert_no_runtime_errors(errors)

    def test_keyboard(self, motion_page: Page):
        page = motion_page
        on, off = choice(page, "on"), choice(page, "off")
        expect(on).to_have_attribute("tabindex", "0")
        expect(off).to_have_attribute("tabindex", "-1")
        # Tab from the theme control reaches the chosen animations choice
        page.locator('[data-verso-theme-toggle] [tabindex="0"]').focus()
        page.keyboard.press("Tab")
        expect(on).to_be_focused()
        assert on.evaluate("e => e.matches(':focus-visible')")
        assert computed(on, "outlineStyle") != "none"
        page.keyboard.press("ArrowRight")
        expect(off).to_be_focused()
        expect(off).to_have_attribute("aria-checked", "true")
        expect(page.locator("html")).to_have_attribute("data-motion", "reduce")
        page.keyboard.press("ArrowLeft")
        expect(on).to_be_focused()
        expect(on).to_have_attribute("aria-checked", "true")
        assert page.evaluate("document.documentElement.getAttribute('data-motion')") is None
        off.focus()
        page.keyboard.press("Space")
        expect(off).to_have_attribute("aria-checked", "true")
        on.focus()
        page.keyboard.press("Enter")
        expect(on).to_have_attribute("aria-checked", "true")

    @pytest.mark.parametrize("scheme", ["light", "dark"])
    def test_contrast(self, motion_page: Page, scheme: str):
        page = motion_page
        page.emulate_media(color_scheme=scheme, reduced_motion="no-preference")
        for which in ("on", "off"):
            choice(page, which).click()
            for el in (page.locator(".bp_motion_label"), choice(page, "on"), choice(page, "off")):
                ratio = el.evaluate(CONTRAST_JS)
                assert ratio >= 4.5, (scheme, which, el, ratio)
        page.emulate_media(color_scheme=scheme, reduced_motion="reduce")
        ratio = page.locator(".bp_motion_note").evaluate(CONTRAST_JS)
        assert ratio >= 4.5, (scheme, ratio)

    def test_phone_width(self, server: str, page: Page):
        errors = record_runtime_errors(page)
        page.set_viewport_size({"width": 390, "height": 844})
        page.emulate_media(reduced_motion="no-preference")
        page.goto(server + MOTION_PAGE)
        assert page.evaluate("document.documentElement.scrollWidth <= document.documentElement.clientWidth")
        expect(live(page).locator("svg")).to_be_visible()
        page.locator("#toggle-toc-click").click()
        expect(control(page)).to_be_in_viewport(ratio=1)
        box = control(page).bounding_box()
        assert box is not None and box["x"] >= 0 and box["x"] + box["width"] <= 390, box
        choice(page, "off").click()
        expect(page.locator("html")).to_have_attribute("data-motion", "reduce")
        expect(stills(page)).to_be_attached()
        assert page.evaluate("document.documentElement.scrollWidth <= document.documentElement.clientWidth")
        assert_no_runtime_errors(errors)

    def test_storage_blocked(self, server: str, page: Page):
        page_errors: list[str] = []
        page.on("pageerror", lambda exc: page_errors.append(str(exc)))
        page.add_init_script(BLOCK_STORAGE)
        page.emulate_media(reduced_motion="no-preference")
        page.goto(server + MOTION_PAGE)
        expect(choice(page, "on")).to_have_attribute("aria-checked", "true")
        choice(page, "off").click()
        expect(page.locator("html")).to_have_attribute("data-motion", "reduce")
        assert computed(live(page), "visibility") == "hidden"
        choice(page, "on").click()
        assert computed(live(page), "visibility") == "visible"
        motion_errors = [e for e in page_errors if "storage" in e.lower() or "motion" in e.lower()]
        assert not motion_errors, motion_errors

    def test_choice_in_another_tab(self, server: str, browser):
        context = browser.new_context(reduced_motion="no-preference")
        try:
            page, other = context.new_page(), context.new_page()
            page.goto(server + MOTION_PAGE)
            other.goto(server + MOTION_PAGE)
            choice(page, "off").click()
            expect(other.locator("html")).to_have_attribute("data-motion", "reduce")
            expect(choice(other, "off")).to_have_attribute("aria-checked", "true")
            choice(page, "on").click()
            expect(choice(other, "on")).to_have_attribute("aria-checked", "true")
            expect(other.locator("html")).not_to_have_attribute("data-motion", "reduce")
        finally:
            context.close()
