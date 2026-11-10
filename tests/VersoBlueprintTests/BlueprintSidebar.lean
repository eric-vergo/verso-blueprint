/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint.Sidebar
import VersoBlueprint.PreviewManifest
import VersoBlueprintTests.Blueprint.Support

namespace Verso.VersoBlueprintTests.BlueprintSidebar

open Verso Genre Manual
open Verso.VersoBlueprintTests.Blueprint.Support

private def sidebarConfig : Informal.Sidebar.Config := {
  links := #[
    { label := "Paper [web]", href := "https://example.org/paper" },
    { label := "Paper [pdf]", href := "https://example.org/paper.pdf" },
    { label := "GitHub </script>", href := "https://github.com/example/project" }
  ]
}

private def headString (cfg : RenderConfig) : String :=
  String.join (cfg.toHtmlConfig.extraHead.map (·.asString)).toList

-- The sidebar announces itself, carries its configuration as JSON, and ships its CSS and JS.
/-- info: true -/
#guard_msgs in
#eval
  let cfg := Informal.Sidebar.withSidebar sidebarConfig {}
  let head := headString cfg
  let css := cfg.toHtmlConfig.toHtmlAssets.extraCss.toArray.map (·.css)
  let js := cfg.toHtmlConfig.toHtmlAssets.extraJs.toArray.map (·.js)
  hasSubstr head "<meta name=\"verso-blueprint-sidebar\"" &&
    hasSubstr head "id=\"verso-blueprint-sidebar-config\"" &&
    hasSubstr head "\"label\":\"Paper [web]\"" &&
    hasSubstr head "\"href\":\"https://example.org/paper.pdf\"" &&
    hasSubstr head "\"homeLabel\":\"Blueprint Home\"" &&
    -- the payload cannot close its script element
    !hasSubstr head "GitHub </script>" && hasSubstr head "GitHub \\u003c/script>" &&
    -- the stored theme is applied before paint
    hasSubstr head "localStorage.getItem(\"verso-theme\")" &&
    css.any (hasSubstr · "html:has(meta[name=\"verso-blueprint-sidebar\"]) #toc") &&
    js.any (hasSubstr · "bp_theme_switch")

-- Applying the sidebar twice does not duplicate its head elements.
/-- info: true -/
#guard_msgs in
#eval
  let once := Informal.Sidebar.withSidebar sidebarConfig {}
  let twice := Informal.Sidebar.withSidebar sidebarConfig once
  countSubstr (headString twice) "verso-blueprint-sidebar-config" == 1

-- Without links the configuration is still emitted (home entry and theme switch).
/-- info: true -/
#guard_msgs in
#eval
  hasSubstr (headString (Informal.Sidebar.withSidebar {} {})) "\"links\":[]"

end Verso.VersoBlueprintTests.BlueprintSidebar
