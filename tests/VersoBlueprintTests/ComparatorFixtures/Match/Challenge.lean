/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/
module

/-!
A Comparator challenge (module system) whose solution proves both theorems with the same
statements: `BlueprintComparator` reads its compiled module.
-/

@[expose] public section

namespace CmpMatch

/-- Twice a number. -/
def double (n : Nat) : Nat := 2 * n

/-- Doubling a number
adds it to itself. -/
theorem double_eq (n : Nat) :
    double n = n + n := by
  sorry

-- A comment between declarations.
theorem double_cases (n : Nat) : double n = 0 ∨ double n ≠ 0 := by
  sorry

end CmpMatch
