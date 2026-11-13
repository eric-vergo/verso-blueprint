/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lake.Build.Module
import Lake.Build.Run
import Lake.Load.Workspace
import VersoBlueprint.Stats.Comparator

/-!
`vbp` builds the project's Comparator challenge before it runs the generator, so that the
statistics' headline compares an up-to-date challenge with the solution. Nothing imports the
challenge (it declares the same names as the solution), so building the generator's imports does
not build it.
-/

namespace VersoBlueprint.Vbp

open System

/--
Build the Comparator challenge module of the workspace rooted at the working directory, when
the workspace has one: the module `comparator.json` names, or `Comparator.Challenge`. Only
errors are reported (the challenge's `sorry` warnings are expected); a challenge that fails to
build is reported and nothing else happens, so the site is still generated.
-/
def buildComparatorChallenge (ws : Lake.Workspace) : IO Unit := do
  let config ← match ← Informal.Stats.ChallengeConfig.atRoot? (← IO.currentDir) with
    | some (.ok config) => pure config
    | some (.error _) => return
    | none => pure {}
  let some mod := ws.findModule? config.challengeModule | return
  try
    let _ ← ws.runBuild mod.leanArts.fetch { outLv := .error }
  catch err =>
    IO.eprintln
      s!"vbp build: the Comparator challenge {config.challengeModule} did not build: {err}"

end VersoBlueprint.Vbp
