/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprintReplayDependency.Lemmas

/-!
A project module over a dependency (`VersoBlueprintReplayDependency.Lemmas`). Every constant of
this module was checked by the kernel when it was compiled. `double_odd` is false all the same:
it rests on the dependency's `helper`, which no kernel accepts. `double_zero` and `uses_fine`
depend on nothing that is wrong, `from_axiom` rests on an axiom of the module's own, and
`unsafeValue` is unsafe code.
-/

namespace ReplayReach

/-- Twice a number. -/
def double (n : Nat) : Nat := 2 * n

/-- Every double is odd (it is not). -/
theorem double_odd (n : Nat) : double n = 2 * n + 1 :=
  False.elim ReplayDependency.helper

/-- Sound, and it depends on nothing of the dependency. -/
theorem double_zero : double 0 = 0 := rfl

/-- Sound, through the dependency's sound lemma. -/
theorem uses_fine : True := ReplayDependency.fine

/-- An assumption of the module's own. -/
axiom assumed : double 1 = 2

/-- Proved only from the assumption. -/
theorem from_axiom : double 1 = 2 := assumed

/-- Code a kernel does not check. -/
unsafe def unsafeValue : Nat := 0

end ReplayReach
