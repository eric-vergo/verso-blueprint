/-! A tiny library about doubling. -/

namespace Demo

/-- Twice a natural number. -/
def double (n : Nat) : Nat := 2 * n

/-- Doubling is adding a number to itself: $2n = n + n$. -/
theorem double_eq (n : Nat) : double n = n + n := by
  unfold double; omega

theorem double_add (a b : Nat) : double (a + b) = double a + double b := by
  unfold double; omega

end Demo
