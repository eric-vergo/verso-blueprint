/*
 * Side-by-side Blueprint nodes: move each proof that directly follows its
 * statement node (and the proof's Lean references panel, if any) into the
 * node's left column, so the statement, its folded proof and the Lean source
 * read as one unit, and show the legend of the status glyphs. Pages without
 * side-by-side nodes are left untouched.
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
        // Inside its node the proof needs no "for <statement>" in its caption.
        const caption = next.querySelector(".bp_heading .bp_caption");
        if (caption) {
          caption.setAttribute("title", caption.textContent.trim());
          caption.textContent = "Proof";
        }
        column.appendChild(next);
        if (after && after.classList.contains("bp_code_panel_wrapper")) {
          const panel = after;
          after = after.nextElementSibling;
          column.appendChild(panel);
        }
        next = after;
      }
    });
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
    installLegend();
    installMathFitting();
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", install);
  } else {
    install();
  }
})();
