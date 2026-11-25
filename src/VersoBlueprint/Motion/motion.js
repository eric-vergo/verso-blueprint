/*
 * The animations switch.
 *
 * A page has motion when it contains an element with the attribute
 * data-bp-motion. Such a page shows a control "Animations [On | Off]" beside
 * the theme control (after the element with the data-verso-theme-toggle
 * attribute, else at the foot of the table of contents, else at the top of the
 * page's main content); a page without motion shows nothing. The control is
 * inserted when the page has been parsed, in the same frame as the theme
 * control is shown, and also when content with motion is added to the page
 * later (a preview, for example).
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
 *
 * A link to "#bp-motion" (a figure's caption may carry one) moves the focus to
 * the control, opening the collapsed table of contents on narrow screens. Such
 * a link with class bp_motion_link is shown only when this script runs (the
 * root element gets the class bp-motion-scripted), since without scripts there
 * is no control to go to.
 */
(function () {
  document.documentElement.classList.add("bp-motion-scripted");

  const storageKey = "verso-blueprint-motion";
  const attribute = "data-motion";
  const systemQuery = "(prefers-reduced-motion: reduce)";
  const motionSelector = "[data-bp-motion]";
  const themeSelector = "[data-verso-theme-toggle]";
  const controlId = "bp-motion";

  function systemQueryList() {
    return window.matchMedia ? window.matchMedia(systemQuery) : null;
  }

  function systemReduces() {
    const query = systemQueryList();
    return !!(query && query.matches);
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
    wrap.id = controlId;
    const label = element("span", "bp_motion_label", "Animations");
    label.id = "bp-motion-label";
    const group = element("div", "bp_motion_toggle");
    group.setAttribute("role", "radiogroup");
    group.setAttribute("aria-labelledby", label.id);
    const note = element("p", "bp_motion_note", "Off because your system settings ask for reduced motion.");
    note.id = "bp-motion-note";
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
        // The note describes the group only while it applies: a hidden note that is still
        // referenced would be read out all the same.
        group.setAttribute("aria-describedby", note.id);
      } else {
        on.removeAttribute("aria-disabled");
        on.title = "Show animations";
        group.removeAttribute("aria-describedby");
      }
      // Only the chosen one is a Tab stop; the arrow keys move between the two.
      on.tabIndex = isOff ? -1 : 0;
      off.tabIndex = isOff ? 0 : -1;
      note.hidden = !system;
    }

    function pick(button) {
      if (button.getAttribute("aria-disabled") === "true") return;
      // Choosing what is already shown changes nothing, and stores nothing.
      if (button.getAttribute("aria-checked") === "true") return;
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

    const query = systemQueryList();
    if (query) {
      if (query.addEventListener) query.addEventListener("change", sync);
      else if (query.addListener) query.addListener(sync);
    }
    // Stay in step with a choice made in another tab of the site.
    new MutationObserver(sync).observe(document.documentElement, {
      attributes: true,
      attributeFilter: [attribute],
    });

    sync();
    group.appendChild(on);
    group.appendChild(off);
    const row = element("div", "bp_motion_row");
    row.appendChild(label);
    row.appendChild(group);
    wrap.appendChild(row);
    wrap.appendChild(note);
    return wrap;
  }

  // Beside the theme control, wherever the page has it.
  function place(control) {
    const theme = document.querySelector(themeSelector);
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

  function installed() {
    return document.getElementById(controlId) !== null;
  }

  // Insert the control if the page has motion. True once the control is there.
  function install() {
    if (installed()) return true;
    if (!document.querySelector(motionSelector)) return false;
    place(build());
    return true;
  }

  function hasMotion(node) {
    return node.nodeType === 1 && (node.matches(motionSelector) || node.querySelector(motionSelector) !== null);
  }

  // After the page has loaded, watch for content with motion added to it.
  function watch() {
    const watcher = new MutationObserver(function (records) {
      const found = records.some(function (record) {
        return Array.prototype.some.call(record.addedNodes, hasMotion);
      });
      if (found && install()) watcher.disconnect();
    });
    watcher.observe(document.body, { childList: true, subtree: true });
  }

  // Move the focus to the control, opening the collapsed table of contents first.
  function reveal() {
    const control = document.getElementById(controlId);
    if (!control) return;
    const toggle = document.getElementById("toggle-toc");
    if (toggle && !toggle.checked && window.matchMedia && window.matchMedia("(max-width: 700px)").matches) {
      toggle.checked = true;
    }
    const target = control.querySelector('[role="radio"][tabindex="0"]');
    if (target) target.focus({ preventScroll: true });
    control.scrollIntoView({ block: "nearest" });
  }

  // The page's <base> may point elsewhere, so a bare "#bp-motion" is taken as this page's.
  function linksToControl(link) {
    if (link.getAttribute("href") === "#" + controlId) return true;
    return link.hash === "#" + controlId && link.pathname === window.location.pathname;
  }

  document.addEventListener("click", function (event) {
    const link = event.target instanceof Element ? event.target.closest("a[href]") : null;
    if (!link || !linksToControl(link) || !installed()) return;
    event.preventDefault();
    reveal();
  });
  window.addEventListener("hashchange", function () {
    if (window.location.hash === "#" + controlId) reveal();
  });

  function init() {
    if (!install()) watch();
  }

  // An address naming the switch: once the page has loaded, when the browser has done its own
  // scrolling to the address.
  window.addEventListener("load", function () {
    if (window.location.hash === "#" + controlId) reveal();
  });

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
