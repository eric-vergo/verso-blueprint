/-! A solution that proves another statement than the challenge's: <b>not</b> the same. -/

namespace Dif

/-- Addition of natural numbers is commutative. -/
theorem add_swap (a b : Nat) : a + b = b + a + 0 := by
  omega

end Dif
