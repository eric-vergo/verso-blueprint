/*
 * Side-by-side Blueprint nodes: move each proof that directly follows its
 * statement node (and the proof's Lean references panel, if any) into the
 * node's left column, so the statement, its folded proof and the Lean source
 * read as one unit. Pages without side-by-side nodes are left untouched.
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

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", attachProofs);
  } else {
    attachProofs();
  }
})();
