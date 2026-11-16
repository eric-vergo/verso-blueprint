/-! The solution: the challenge's theorem, proved. -/

namespace Cmp

/-- Twice a natural number. -/
def double (n : Nat) : Nat := 2 * n

/-- Doubling gives an even number. -/
theorem double_even (n : Nat) : double n % 2 = 0 := by
  unfold double; omega

end Cmp
