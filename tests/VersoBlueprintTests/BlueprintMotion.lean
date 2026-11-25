/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint.Motion
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
    css.any (hasSubstr · ".bp_motion_stills") &&
    -- hidden without stopping the animation's clock
    css.any (hasSubstr · "visibility: hidden") &&
    js.any (hasSubstr · "[data-bp-motion], .pilean-motion")

-- Applying it twice does not duplicate the early script.
/-- info: true -/
#guard_msgs in
#eval
  let twice := Informal.Motion.withMotion (Informal.Motion.withMotion {})
  countSubstr (headString twice) "verso-blueprint-motion" == 1

end Verso.VersoBlueprintTests.BlueprintMotion
