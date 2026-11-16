/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprint.Stats.Comparator

/-!
The kernel replay's worker as a program of its own, for the tests: `BlueprintKernelReplay` runs
it with `lean --run`, a request file and a reply file, so that the compiled modules are loaded
in another process than the one that compiles the tests (`Informal.Stats.replayWorkerMain`).
-/

def main (args : List String) : IO UInt32 :=
  Informal.Stats.replayWorkerMain args
