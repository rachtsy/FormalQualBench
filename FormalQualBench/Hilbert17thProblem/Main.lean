import Mathlib

namespace Hilbert17thProblem

open scoped BigOperators

noncomputable section

/-- A multivariate real polynomial is *globally nonnegative* if it evaluates to a nonnegative real
number at every point. -/
def IsGloballyNonnegative {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, 0 ≤ p.eval x

/-- Artin's solution to Hilbert's 17th problem (statement): a globally nonnegative real polynomial
is the sum of squares of rational functions. -/
theorem MainTheorem (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : IsGloballyNonnegative p) :
    ∃ m : ℕ,
      ∃ f : Fin m → FractionRing (MvPolynomial (Fin n) ℝ),
        algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) p =
          ∑ i : Fin m, (f i) ^ 2 := by
  sorry

end

end Hilbert17thProblem
