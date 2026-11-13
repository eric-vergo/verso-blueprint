/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

/-! A Comparator challenge whose solution changes a definition the statement uses. -/

namespace CmpDefinition

/-- The square of a number. -/
def square (n : Nat) : Nat := n * n

/-- The square of two is four. -/
theorem square_two : square 2 = 4 := by
  sorry

end CmpDefinition
