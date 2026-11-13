/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

/-! The solution of `ComparatorFixtures.Hole.Challenge`. -/

namespace CmpHole

/-- The answer, which the solution chooses. -/
def answer : Nat := 42

/-- The answer is positive. -/
theorem answer_pos : 0 < answer := by
  decide

end CmpHole
