/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint.Informal.Block.Assets
import VersoBlueprintTests.Blueprint.Support

namespace Verso.VersoBlueprintTests.BlueprintDarkTheme

open Verso.VersoBlueprintTests.Blueprint.Support

/-- Names of the custom properties (`--name`) declared in the first `{ ... }` block of `css`. -/
private def declaredNames (css : String) : List String :=
  let body := ((css.splitOn "{").getD 1 "").splitOn "}" |>.head!
  (body.splitOn "\n").filterMap fun line =>
    let line := line.trimAscii.toString
    if line.startsWith "--" then (line.splitOn ":").head? else none

private def lightNames : List String :=
  (declaredNames Informal.Commands.blueprintLightTokensCss).filter fun name =>
    name.startsWith "--bp-" && !name.startsWith "--bp-radius-"

private def attributeBlock : String :=
  (Informal.Commands.blueprintDarkTokensCss.splitOn "@media").head!

private def mediaBlock : String :=
  (Informal.Commands.blueprintDarkTokensCss.splitOn "@media (prefers-color-scheme: dark) {\n").getD 1 ""

/-- info: true -/
#guard_msgs in
#eval
  let dark := Informal.Commands.darkTokens.map (·.1)
  !lightNames.isEmpty && lightNames.all dark.contains

/-- info: true -/
#guard_msgs in
#eval
  let css := Informal.Commands.blueprintDarkTokensCss
  hasSubstr css "html[data-theme=\"dark\"]" &&
  hasSubstr css "@media (prefers-color-scheme: dark)" &&
  hasSubstr css "html:not([data-theme=\"light\"])"

/-- info: true -/
#guard_msgs in
#eval
  let names (css : String) := (declaredNames css).filter (·.startsWith "--")
  names attributeBlock == names mediaBlock &&
    names attributeBlock == (Informal.Commands.darkTokens.map (·.1)).filter (·.startsWith "--")

/-- info: true -/
#guard_msgs in
#eval
  Informal.Block.Assets.blockCssAssets.any fun css =>
    hasSubstr css Informal.Commands.blueprintDarkTokensCss

end Verso.VersoBlueprintTests.BlueprintDarkTheme
