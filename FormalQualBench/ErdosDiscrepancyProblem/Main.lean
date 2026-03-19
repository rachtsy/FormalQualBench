import Mathlib

namespace ErdosDiscrepancyProblem

open scoped BigOperators

def IsSign (z : ℤ) : Prop :=
  z = 1 ∨ z = -1

/-- Tao's solution of the Erdős discrepancy problem. -/
def DiscrepancyUnbounded : Prop :=
  ∀ f : ℕ → ℤ, (∀ n, IsSign (f n)) →
    ∀ C : ℕ, ∃ d n : ℕ, 0 < d ∧ 0 < n ∧
      C < Int.natAbs (∑ i ∈ Finset.Icc (1 : ℕ) n, f (i * d))

theorem MainTheorem : DiscrepancyUnbounded := by
  sorry

end ErdosDiscrepancyProblem
