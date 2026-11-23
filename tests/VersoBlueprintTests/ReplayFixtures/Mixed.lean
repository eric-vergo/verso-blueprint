/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

/-!
A project with an open proof. `sound` is proved; `open_step` is not (`sorry`); `uses_open`
depends on `open_step`. Both checkers decline a whole export that uses `sorryAx`, so a replay
leaves the last two out and still checks the first.
-/

namespace ReplayMixed

/-- Proved. -/
theorem sound : 2 + 2 = 4 := rfl

set_option warn.sorry false in
/-- Not proved yet. -/
theorem open_step : ∀ n : Nat, n + 0 = n := sorry

/-- Proved from the open step. -/
theorem uses_open : 3 + 0 = 3 := open_step 3

end ReplayMixed
