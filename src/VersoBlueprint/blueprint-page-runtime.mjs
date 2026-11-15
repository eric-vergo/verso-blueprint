import { createPreview } from "./api/preview.mjs";
import { installOpenTargetDetails } from "./Commands/open-target-details.mjs";
import { startGraphRuntime } from "./Commands/graph.mjs";
import { startInlinePreview } from "./Commands/inline-preview.mjs";
import { startRelationPanels } from "./Informal/Block/relation-panel.mjs";

/**
 * A click on the backdrop behind the contents panel (narrow windows) closes the panel, as the
 * theme's own handler attribute does. Bound from this script it also works on pages where
 * handler attributes are not run; the attribute is removed first, so a click acts once.
 * @param {Document | undefined} doc
 */
export function installTocBackdrop(doc = globalThis.document) {
  if (!doc) return;
  for (const backdrop of doc.querySelectorAll(".toc-backdrop")) {
    backdrop.removeAttribute("onclick");
    backdrop.addEventListener("click", () => {
      const toggle = doc.getElementById("toggle-toc-click");
      if (toggle) toggle.click();
    });
  }
}

export function startBlueprintPageRuntime(options = {}) {
  const preview = createPreview(options);
  installOpenTargetDetails(globalThis);
  installTocBackdrop(globalThis.document);
  startInlinePreview(preview);
  startRelationPanels(preview);
  startGraphRuntime(preview);
  return preview;
}

export const blueprintPageRuntime = startBlueprintPageRuntime();

export default {
  blueprintPageRuntime,
  installTocBackdrop,
  startBlueprintPageRuntime,
};
