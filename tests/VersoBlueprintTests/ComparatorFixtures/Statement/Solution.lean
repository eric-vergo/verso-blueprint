/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

/-! The solution of `ComparatorFixtures.Statement.Challenge`, proving a weaker statement. -/

namespace CmpStatement

/-- Half a number, rounded down. -/
def half (n : Nat) : Nat := n / 2

/-- Half a number is at most one more than the number. -/
theorem half_le (n : Nat) : half n ≤ n + 1 :=
  Nat.le_succ_of_le (Nat.div_le_self n 2)

end CmpStatement
