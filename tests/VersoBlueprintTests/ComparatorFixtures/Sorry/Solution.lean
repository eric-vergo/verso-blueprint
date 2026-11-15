/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

/-! The solution of `ComparatorFixtures.Sorry.Challenge`, with its proof left out. -/

namespace CmpSorry

/-- Three times a number. -/
def triple (n : Nat) : Nat := 3 * n

/-- Tripling is adding three times. -/
theorem triple_eq (n : Nat) : triple n = n + n + n := by
  sorry

end CmpSorry
