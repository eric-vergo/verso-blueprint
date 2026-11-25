/*
 * The animations switch.
 *
 * A page has motion when it contains an element with the attribute
 * data-bp-motion (or the class pilean-motion). Such a page shows a control
 * "Animations: On | Off" beside the theme control (after the element with the
 * data-verso-theme-toggle attribute, else at the foot of the table of
 * contents); a page without motion shows nothing.
 *
 * "Off" sets data-motion="reduce" on the root element and stores "reduce" in
 * localStorage under "verso-blueprint-motion"; "On" removes both, so that the
 * reader's system setting (prefers-reduced-motion) decides. The choice applies
 * to every page of the site: an inline <head> script sets the attribute before
 * the page is drawn. When the system asks for reduced motion, "Off" is shown
 * chosen and "On" cannot be chosen, with a note saying why: the switch can ask
 * for less motion than the system, never for more.
 *
 * The two choices are radio buttons in a radio group: Tab reaches the chosen
 * one, and the arrow keys move to the other and choose it.
 */
(function () {
  const storageKey = "verso-blueprint-motion";
  const attribute = "data-motion";
  const systemQuery = "(prefers-reduced-motion: reduce)";
  const motionSelector = "[data-bp-motion], .pilean-motion";

  function systemReduces() {
    return !!(window.matchMedia && window.matchMedia(systemQuery).matches);
  }

  function chosenOff() {
    return document.documentElement.getAttribute(attribute) === "reduce";
  }

  function apply(off) {
    const root = document.documentElement;
    if (off) root.setAttribute(attribute, "reduce");
    else root.removeAttribute(attribute);
  }

  function choose(off) {
    apply(off);
    try {
      if (off) localStorage.setItem(storageKey, "reduce");
      else localStorage.removeItem(storageKey);
    } catch (_err) {
      // Without storage the choice lasts for this page only.
    }
  }

  function element(tag, className, text) {
    const el = document.createElement(tag);
    if (className) el.className = className;
    if (text !== undefined) el.textContent = text;
    return el;
  }

  function build() {
    const wrap = element("div", "bp_motion");
    const group = element("div", "bp_motion_toggle");
    group.setAttribute("role", "radiogroup");
    const label = element("span", "bp_motion_label", "Animations");
    label.id = "bp-motion-label";
    group.setAttribute("aria-labelledby", label.id);
    const note = element("p", "bp_motion_note", "Off because your system settings ask for reduced motion.");
    note.id = "bp-motion-note";
    group.setAttribute("aria-describedby", note.id);
    const on = element("button", "", "On");
    const off = element("button", "", "Off");
    on.setAttribute("data-motion-choice", "on");
    off.setAttribute("data-motion-choice", "off");
    off.title = "Show still pictures instead of animations";
    const buttons = [on, off];
    buttons.forEach(function (button) {
      button.type = "button";
      button.setAttribute("role", "radio");
    });

    function sync() {
      const system = systemReduces();
      const isOff = system || chosenOff();
      on.setAttribute("aria-checked", isOff ? "false" : "true");
      off.setAttribute("aria-checked", isOff ? "true" : "false");
      if (system) {
        on.setAttribute("aria-disabled", "true");
        on.title = "Your system settings ask for reduced motion";
      } else {
        on.removeAttribute("aria-disabled");
        on.title = "Show animations";
      }
      // Only the chosen one is a Tab stop; the arrow keys move between the two.
      on.tabIndex = isOff ? -1 : 0;
      off.tabIndex = isOff ? 0 : -1;
      note.hidden = !system;
    }

    function pick(button) {
      if (button.getAttribute("aria-disabled") === "true") return;
      choose(button === off);
      sync();
    }

    buttons.forEach(function (button, index) {
      button.addEventListener("click", function () {
        pick(button);
      });
      button.addEventListener("keydown", function (event) {
        if (!["ArrowLeft", "ArrowRight", "ArrowUp", "ArrowDown"].includes(event.key)) return;
        event.preventDefault();
        const next = buttons[1 - index];
        if (next.getAttribute("aria-disabled") === "true") return;
        next.focus();
        pick(next);
      });
    });

    if (window.matchMedia) {
      const query = window.matchMedia(systemQuery);
      if (query.addEventListener) query.addEventListener("change", sync);
    }
    // Stay in step with a choice made in another tab of the site.
    new MutationObserver(sync).observe(document.documentElement, {
      attributes: true,
      attributeFilter: [attribute],
    });

    sync();
    group.appendChild(label);
    group.appendChild(on);
    group.appendChild(off);
    wrap.appendChild(group);
    wrap.appendChild(note);
    return wrap;
  }

  // Beside the theme control, wherever the page has it.
  function place(control) {
    const theme = document.querySelector("[data-verso-theme-toggle]");
    if (theme && theme.parentNode) {
      theme.parentNode.insertBefore(control, theme.nextSibling);
      return;
    }
    const toc = document.getElementById("toc");
    if (toc) {
      (toc.querySelector(":scope > .last") || toc).appendChild(control);
      return;
    }
    const main = document.querySelector("main") || document.body;
    main.insertBefore(control, main.firstChild);
  }

  function init() {
    if (!document.querySelector(motionSelector) || document.querySelector(".bp_motion")) return;
    place(build());
  }

  window.addEventListener("storage", function (event) {
    if (event.key !== storageKey && event.key !== null) return;
    apply(event.key !== null && event.newValue === "reduce");
  });

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
})();
