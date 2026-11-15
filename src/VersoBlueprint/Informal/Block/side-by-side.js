/*
 * Side-by-side Blueprint nodes. The generator places each proof that directly
 * follows its statement node in the node's left column; on pages built without
 * that, this script moves the proof (and the proof's Lean references panel, if
 * any) there. It also shows the legend of the status glyphs, and links each
 * node's proof toggles: "Proof [show]" on the prose side opens and closes the
 * prose proof and the node's Lean proofs together, with a short height
 * animation. Without this script every proof keeps its own native toggle.
 * Pages without side-by-side nodes are left untouched.
 */
(function () {
  function attachProofs() {
    const nodes = document.querySelectorAll(".bp_sbs[data-bp-node]");
    nodes.forEach(function (node) {
      const column = node.querySelector(":scope > .bp_sbs_grid > .bp_sbs_informal");
      if (!column) return;
      const label = node.getAttribute("data-bp-node");
      let next = node.nextElementSibling;
      while (
        next &&
        next.getAttribute("data-bp-facet") === "proof" &&
        next.getAttribute("data-bp-node") === label
      ) {
        let after = next.nextElementSibling;
        column.appendChild(next);
        if (after && after.classList.contains("bp_code_panel_wrapper")) {
          const panel = after;
          after = after.nextElementSibling;
          column.appendChild(panel);
        }
        next = after;
      }
      // Inside its node the proof needs no "for <statement>" in its caption.
      column.querySelectorAll(':scope > [data-bp-facet="proof"] > .bp_heading .bp_caption').forEach(
        function (caption) {
          if (caption.textContent.trim() === "Proof") return;
          caption.setAttribute("title", caption.textContent.trim());
          caption.textContent = "Proof";
        }
      );
    });
  }

  // Proof toggles. A `<details>` opens and closes through `setOpen`, which
  // animates its height from where it is now, so a second press reverses a
  // running animation. Every animation takes `--bp-sbs-proof-duration`, so a
  // node's proofs move in step and a long proof is no slower than a short one;
  // with reduced motion the change is immediate.
  const reducedMotion = window.matchMedia
    ? window.matchMedia("(prefers-reduced-motion: reduce)")
    : { matches: false };

  function motionSettings(element) {
    const style = window.getComputedStyle(element);
    const durationText = style.getPropertyValue("--bp-sbs-proof-duration").trim();
    let duration = parseFloat(durationText);
    if (isNaN(duration)) duration = 200;
    else if (!/ms$/.test(durationText)) duration *= 1000;
    return {
      duration: duration,
      easing: style.getPropertyValue("--bp-sbs-proof-easing").trim() || "ease-out"
    };
  }

  function finish(details) {
    const animation = details._bpAnimation;
    details._bpAnimation = null;
    if (animation) animation.cancel();
    details.removeAttribute("data-bp-animating");
    details.removeAttribute("data-bp-closing");
  }

  // Whether the toggle is heading to open (a closing animation counts as closed).
  function isOpening(details) {
    return details.open && !details.hasAttribute("data-bp-closing");
  }

  function setOpen(details, open, animate) {
    if (isOpening(details) === open) return;
    const startHeight = details.getBoundingClientRect().height;
    finish(details);
    const settings = motionSettings(details);
    // A page that is not visible (a background tab or view) has nothing to animate, and its
    // animation clock may not run.
    const canAnimate =
      animate && !reducedMotion.matches && settings.duration > 0 &&
      document.visibilityState === "visible" && typeof details.animate === "function";
    if (!canAnimate) {
      details.open = open;
      return;
    }
    // The heights at both ends (a closed Lean proof whose toggle gives way takes no room).
    details.open = false;
    const closedHeight = details.getBoundingClientRect().height;
    details.open = true;
    const openHeight = details.getBoundingClientRect().height;
    if (!open) details.setAttribute("data-bp-closing", "");
    details.setAttribute("data-bp-animating", "");
    const animation = details.animate(
      [{ height: startHeight + "px" }, { height: (open ? openHeight : closedHeight) + "px" }],
      { duration: settings.duration, easing: settings.easing }
    );
    details._bpAnimation = animation;
    animation.onfinish = function () {
      if (details._bpAnimation !== animation) return;
      finish(details);
      details.open = open;
    };
  }

  function onToggleClick(summary, handler) {
    summary.addEventListener("click", function (event) {
      // Links and buttons inside the toggle keep their own behaviour.
      const inner = event.target.closest("a, button, input, select, textarea");
      if (inner && summary.contains(inner)) return;
      event.preventDefault();
      handler();
    });
  }

  let nextProofId = 0;

  function linkProofs(node) {
    if (node.closest(".bp_node_view")) return;
    const column = node.querySelector(":scope > .bp_sbs_grid > .bp_sbs_informal");
    const formal = node.querySelector(":scope > .bp_sbs_grid > .bp_sbs_formal");
    const prose = column
      ? column.querySelectorAll(":scope > details.bp_kind_proof_wrapper")
      : [];
    const lean = formal ? formal.querySelectorAll("details.bp_decl_source_proof") : [];
    const controller = prose[0];
    const linked = Boolean(controller) && lean.length > 0;
    // Each proof animates on its own toggle; the first prose proof also drives
    // the node's Lean proofs.
    const toggles = Array.prototype.slice.call(prose).concat(Array.prototype.slice.call(lean));
    toggles.forEach(function (details) {
      const summary = details.querySelector(":scope > summary");
      if (!summary) return;
      summary.setAttribute("aria-expanded", details.open ? "true" : "false");
      onToggleClick(summary, function () {
        const open = !isOpening(details);
        summary.setAttribute("aria-expanded", open ? "true" : "false");
        setOpen(details, open, true);
        if (linked && details === controller) {
          lean.forEach(function (partner) {
            setOpen(partner, open, true);
          });
        }
      });
      // Opened or closed another way (a link into the proof, find in page).
      details.addEventListener("toggle", function () {
        if (details._bpAnimation) return;
        summary.setAttribute("aria-expanded", details.open ? "true" : "false");
      });
    });
    if (!linked) return;
    node.setAttribute("data-bp-proofs-linked", "");
    const ids = Array.prototype.map.call(lean, function (details) {
      if (!details.id) details.id = "bp-lean-proof-" + nextProofId++;
      return details.id;
    });
    const summary = controller.querySelector(":scope > summary");
    if (summary) summary.setAttribute("aria-controls", ids.join(" "));
    // The Lean proofs follow the prose proof when it opens or closes another way.
    controller.addEventListener("toggle", function () {
      if (controller._bpAnimation) return;
      lean.forEach(function (details) {
        if (!details._bpAnimation) details.open = controller.open;
      });
    });
  }

  // Ends a running animation at its end state.
  function settle(details) {
    const animation = details._bpAnimation;
    if (!animation) return;
    const open = !details.hasAttribute("data-bp-closing");
    finish(details);
    details.open = open;
  }

  function installProofToggles() {
    document.querySelectorAll(".bp_sbs[data-bp-node]").forEach(linkProofs);
    // A page that is hidden mid-animation settles at once.
    document.addEventListener("visibilitychange", function () {
      if (document.visibilityState === "visible") return;
      document.querySelectorAll("details[data-bp-animating]").forEach(settle);
    });
  }

  // A link into a proof opens it (and, through the toggle link, its partners).
  function openTarget() {
    const id = decodeURIComponent((window.location.hash || "").slice(1));
    if (!id) return;
    const target = document.getElementById(id);
    if (!target) return;
    let details = target.closest("details");
    while (details) {
      if (!details.open) details.open = true;
      details = details.parentElement ? details.parentElement.closest("details") : null;
    }
  }

  // The status glyph legend ships as a template element with id
  // "bp-status-legend" in the page head. On pages
  // with glyphs it goes to the sidebar foot when there is one (see the sidebar
  // script, which also adopts it if it runs later), else to the end of the page.
  function installLegend() {
    const template = document.getElementById("bp-status-legend");
    if (!template || !document.querySelector(".bp_status_glyph")) return;
    if (document.querySelector(".bp_status_legend")) return;
    const legend = template.content.firstElementChild;
    if (!legend) return;
    const host =
      document.querySelector(".bp_sidebar_foot_extra") ||
      document.querySelector("main .content-wrapper > section") ||
      document.querySelector("main");
    if (host) host.appendChild(legend.cloneNode(true));
  }

  // Display formulas wider than the informal column are set smaller to fit,
  // down to 70% of their size; wider ones still scroll inside the column.
  const minMathScale = 0.7;

  function fitDisplayMath(column) {
    column.querySelectorAll(".katex-display > .katex").forEach(function (math) {
      math.style.fontSize = "";
      const available = math.parentElement.clientWidth;
      const needed = math.scrollWidth;
      if (available <= 0 || needed <= available) return;
      const scale = Math.max(minMathScale, available / needed);
      const size = parseFloat(window.getComputedStyle(math).fontSize);
      math.style.fontSize = (size * scale).toFixed(2) + "px";
    });
  }

  function installMathFitting() {
    const columns = document.querySelectorAll(".bp_sbs_informal");
    if (columns.length === 0) return;
    const fitAll = function () {
      columns.forEach(fitDisplayMath);
    };
    // Formulas are typeset by a later script; fit them once the page has loaded
    // and whenever a column changes width.
    if (document.readyState === "complete") fitAll();
    else window.addEventListener("load", fitAll);
    if (window.ResizeObserver) {
      let lastWidths = new WeakMap();
      const observer = new ResizeObserver(function (entries) {
        entries.forEach(function (entry) {
          const width = Math.round(entry.contentRect.width);
          if (lastWidths.get(entry.target) === width) return;
          lastWidths.set(entry.target, width);
          fitDisplayMath(entry.target);
        });
      });
      columns.forEach(function (column) {
        observer.observe(column);
      });
    }
  }

  function install() {
    attachProofs();
    installProofToggles();
    openTarget();
    window.addEventListener("hashchange", openTarget);
    installLegend();
    installMathFitting();
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", install);
  } else {
    install();
  }
})();
