/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

/-! The solution of `ComparatorFixtures.Definition.Challenge`, with `square` redefined. -/

namespace CmpDefinition

/-- The square of a number. -/
def square (n : Nat) : Nat := n + n

/-- The square of two is four. -/
theorem square_two : square 2 = 4 := rfl

end CmpDefinition
