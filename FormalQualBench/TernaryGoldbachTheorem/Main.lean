import Mathlib.Data.Nat.Prime.Basic

namespace TernaryGoldbachTheorem

/-- Helfgott's ternary Goldbach theorem. -/
theorem MainTheorem :
    ∀ n : ℕ,
      n % 2 = 1 →
        5 < n → ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ n = p + q + r := by
  sorry

end TernaryGoldbachTheorem
