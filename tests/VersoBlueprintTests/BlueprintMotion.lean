/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint.Motion
import VersoBlueprint.LinkCheck
import VersoBlueprintTests.Blueprint.Support

namespace Verso.VersoBlueprintTests.BlueprintMotion

open Verso Genre Manual
open Verso.VersoBlueprintTests.Blueprint.Support

private def headString (cfg : RenderConfig) : String :=
  String.join (cfg.toHtmlConfig.extraHead.map (·.render)).toList

-- Every page applies a stored choice in `<head>`, and ships the hook classes and the switch.
/-- info: true -/
#guard_msgs in
#eval
  let cfg := Informal.Motion.withMotion {}
  let head := headString cfg
  let css := cfg.toHtmlConfig.toHtmlAssets.extraCss.toArray.map (·.css)
  let js := cfg.toHtmlConfig.toHtmlAssets.extraJs.toArray.map (·.js)
  hasSubstr head "<script>" &&
    hasSubstr head "localStorage.getItem(\"verso-blueprint-motion\")===\"reduce\"" &&
    hasSubstr head "setAttribute(\"data-motion\",\"reduce\")" &&
    -- a blocked storage leaves the page as the system setting has it
    hasSubstr head "catch(e){}" &&
    css.any (hasSubstr · "html[data-motion=\"reduce\"] .bp_motion_live") &&
    css.any (hasSubstr · "@media (prefers-reduced-motion: reduce)") &&
    -- the stills are shown by lifting their hiding, keeping the display their producer gives
    css.any (hasSubstr · "html:not([data-motion=\"reduce\"]) .bp_motion_stills") &&
    !css.any (hasSubstr · "display: block") &&
    css.any (hasSubstr · "@media print") &&
    -- hidden without stopping the animation's clock
    css.any (hasSubstr · "visibility: hidden") &&
    js.any (hasSubstr · "\"[data-bp-motion]\"") &&
    !js.any (hasSubstr · "pilean")

-- Applying it twice does not duplicate the early script.
/-- info: true -/
#guard_msgs in
#eval
  let twice := Informal.Motion.withMotion (Informal.Motion.withMotion {})
  countSubstr (headString twice) "verso-blueprint-motion" == 1

-- A link to the switch on its own page is not a dead link, although the switch is created by the
-- page's script; the same place on another page, or another bare place, is still checked.
/-- info: true -/
#guard_msgs in
#eval
  let check := Informal.LinkCheck.resolve ["Chapter"] (some "../")
  Informal.LinkCheck.scriptPlaces.contains Informal.Motion.controlId &&
    (check ("#" ++ Informal.Motion.controlId)).isNone &&
    (check "#elsewhere").isSome &&
    (check ("Other/#" ++ Informal.Motion.controlId)).isSome

end Verso.VersoBlueprintTests.BlueprintMotion
