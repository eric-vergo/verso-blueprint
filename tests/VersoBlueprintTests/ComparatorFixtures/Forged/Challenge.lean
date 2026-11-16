/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

/-!
A Comparator challenge with a false statement, for the solution that forges its proof
(`ComparatorFixtures.Forged.Solution`): `BlueprintKernelReplay` reads its compiled module.
-/

namespace CmpForged

/-- Twice a number. -/
def double (n : Nat) : Nat := 2 * n

/-- Every double is odd (it is not). -/
theorem double_odd (n : Nat) : double n = 2 * n + 1 := by
  sorry

end CmpForged
