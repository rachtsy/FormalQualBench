import Mathlib.Data.Nat.Prime.Basic

namespace MaynardTaoBoundedPrimeGaps

/-- The Maynard-Tao bounded prime gaps theorem: there is a finite bound `B` such that arbitrarily
large pairs of distinct primes differ by at most `B`. -/
theorem MainTheorem :
    ∃ B : ℕ, 0 < B ∧
      ∀ N : ℕ, ∃ p q : ℕ,
        N ≤ p ∧ Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ q - p ≤ B := by
  sorry

end MaynardTaoBoundedPrimeGaps
