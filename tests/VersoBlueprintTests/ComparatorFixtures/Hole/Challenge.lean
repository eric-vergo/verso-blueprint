/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

/-! A Comparator challenge with a definition hole: the solution supplies the value of `answer`. -/

namespace CmpHole

/-- The answer, which the solution chooses. -/
def answer : Nat := sorry

/-- The answer is positive. -/
theorem answer_pos : 0 < answer := by
  sorry

end CmpHole
