/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import Lean

/-!
A solution whose proof no kernel accepts. With `debug.skipKernelTC` a declaration is added to
the environment unchecked: `sneaky` claims `False` with the value `True.intro`. The theorem that
uses it elaborates without an error, has no `sorry` and depends on no axiom, so the compiled
module reports everything a comparison asks for. Only a kernel replay of the module finds the
mismatch, which is what `BlueprintKernelReplay` tests.
-/

namespace CmpForged

open Lean Elab Command in
set_option debug.skipKernelTC true in
run_cmd liftCoreM do
  addDecl <| .thmDecl {
    name := `CmpForged.sneaky, levelParams := [], type := mkConst ``False
    value := mkConst ``True.intro }

/-- Twice a number. -/
def double (n : Nat) : Nat := 2 * n

/-- Every double is odd (it is not). -/
theorem double_odd (n : Nat) : double n = 2 * n + 1 :=
  False.elim sneaky

end CmpForged
