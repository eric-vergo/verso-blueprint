/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoManual
import VersoBlueprint.Html

/-!
A site-wide switch that turns animations off, for pages whose figures move by themselves.

Every page of a Blueprint site carries a small stylesheet, a script and an inline `<head>` script.
The root element's `data-motion` attribute says whether animations are shown: `"reduce"` means they
are not; without it (or with `"auto"`) the reader's system setting (`prefers-reduced-motion`)
decides. The inline script applies a stored choice before the page is drawn, the way the theme's
does, so that an animation never plays for a moment before it is hidden.

A page has motion when it contains an element with the attribute `data-bp-motion` (or the class
`pilean-motion`); only such a page shows the switch, beside the theme control. The stylesheet gives
figure producers two hook classes: an element with class `bp_motion_live` is hidden and one with
class `bp_motion_stills` shown while motion is off.
-/

namespace Informal.Motion

open Verso.Genre.Manual

/-- The `localStorage` key that holds the reader's choice: `"reduce"`, or nothing. -/
def storageKey : String := "verso-blueprint-motion"

/-- The attribute of the root element that says whether animations are shown. -/
def rootAttribute : String := "data-motion"

def css : String := include_str "Motion/motion.css"

def js : String := include_str "Motion/motion.js"

/--
Inline `<head>` script that applies a stored choice before the page is painted, so that an
animation the reader turned off is never seen moving.
-/
def initScript : String :=
  s!"(function()\{try\{if(localStorage.getItem(\"{storageKey}\")===\"reduce\")" ++
  s!"document.documentElement.setAttribute(\"{rootAttribute}\",\"reduce\");}catch(e)\{}})();"

/-- The `<head>` element that applies the stored choice. -/
def headHtml : Verso.Output.Html :=
  .element "script" #[] (.raw initScript)

/-- Give every page of a site the motion switch, its hook classes and the early script. -/
def withMotion (config : RenderConfig) : RenderConfig :=
  let htmlConfig := config.toHtmlConfig
  let assets : HtmlAssets := { extraCss := [css], extraJs := [js] }
  { config with
    toHtmlConfig := {
      htmlConfig with
      toHtmlAssets := htmlConfig.toHtmlAssets.combine assets
      extraHead := VersoBlueprint.Html.pushIfRenderedMissing htmlConfig.extraHead headHtml
    }
  }

end Informal.Motion
