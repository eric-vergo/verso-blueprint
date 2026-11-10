/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean.Data.Json
import VersoManual
import VersoBlueprint.Html

/-!
A navigation sidebar for Blueprint sites, built from Verso's table of contents.

When a generator enables it, every page announces it with
`<meta name="verso-blueprint-sidebar">` and carries a small JSON configuration;
the sidebar stylesheet restyles Verso's table of contents (chapters as a flat
numbered list, the current chapter bold), and the sidebar script adds a
"Blueprint Home" entry, separators, the configured external links and a
light/dark theme switch at the foot. Without JavaScript the restyled table of
contents still works.
-/

namespace Informal.Sidebar

open Lean
open Verso.Genre.Manual

/-- An external link shown in the sidebar, such as a paper or the source repository. -/
structure Link where
  label : String
  href : String
deriving Inhabited, Repr, BEq

/-- Sidebar configuration for a Blueprint site. -/
structure Config where
  /-- Label of the entry that links to the site's front page. -/
  homeLabel : String := "Blueprint Home"
  /-- External links, shown after the table of contents in this order. -/
  links : Array Link := #[]
deriving Inhabited, Repr, BEq

def metaName : String := "verso-blueprint-sidebar"

def configElementId : String := "verso-blueprint-sidebar-config"

def css : String := include_str "Sidebar/sidebar.css"

def js : String := include_str "Sidebar/sidebar.js"

/-- The JSON configuration read by the sidebar script. -/
def Config.toJson (cfg : Config) : Json :=
  Json.mkObj [
    ("homeLabel", cfg.homeLabel),
    ("links", Json.arr (cfg.links.map fun link =>
      Json.mkObj [("label", link.label), ("href", link.href)]))
  ]

/--
Inline `<head>` script that applies a stored theme choice before the page is
painted, so that a dark choice does not flash light on load.
-/
def themeInitScript : String :=
  "(function(){try{var t=localStorage.getItem(\"verso-theme\");" ++
  "if(t===\"dark\"||t===\"light\")document.documentElement.setAttribute(\"data-theme\",t);}" ++
  "catch(e){}})();"

/-- The `<head>` elements that enable the sidebar. -/
def headHtml (cfg : Config) : Array Verso.Output.Html :=
  -- `<` cannot occur in the JSON payload's markup context once escaped this way.
  let json := (cfg.toJson.compress.replace "<" "\\u003c")
  #[
    .tag "meta" #[("name", metaName), ("content", "on")] .empty,
    .tag "script" #[("type", "application/json"), ("id", configElementId)] (.text false json),
    .tag "script" #[] (.text false themeInitScript)
  ]

/-- Enable the sidebar for a generated site. -/
def withSidebar (cfg : Config) (config : RenderConfig) : RenderConfig :=
  let htmlConfig := config.toHtmlConfig
  let assets : HtmlAssets := { extraCss := [css], extraJs := [js] }
  { config with
    toHtmlConfig := {
      htmlConfig with
      toHtmlAssets := htmlConfig.toHtmlAssets.combine assets
      extraHead := headHtml cfg |>.foldl VersoBlueprint.Html.pushIfRenderedMissing htmlConfig.extraHead
    }
  }

end Informal.Sidebar
