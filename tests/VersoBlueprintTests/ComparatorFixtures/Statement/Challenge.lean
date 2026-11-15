/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

/-! A Comparator challenge whose solution proves a weaker statement. -/

namespace CmpStatement

/-- Half a number, rounded down. -/
def half (n : Nat) : Nat := n / 2

/-- Half a number is at most the number. -/
theorem half_le (n : Nat) : half n ≤ n := by
  sorry

end CmpStatement
