import Mathlib.Data.Nat.Prime.Basic

namespace GreenTaoTheorem

/-- Green-Tao theorem: the primes contain arbitrarily long arithmetic progressions. -/
theorem MainTheorem :
    ∀ k : ℕ, ∃ a d : ℕ, 0 < d ∧ ∀ i : Fin k, Nat.Prime (a + i.1 * d) := by
  sorry

end GreenTaoTheorem
