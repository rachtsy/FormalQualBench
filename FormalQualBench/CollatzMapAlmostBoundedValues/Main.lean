import Mathlib

namespace CollatzMapAlmostBoundedValues

open Filter
open scoped BigOperators

/-- Collatz map on `ℕ`: `n ↦ n/2` if `n` is even, and `n ↦ 3n+1` if `n` is odd. -/
def collatz (n : ℕ) : ℕ :=
  if Even n then n / 2 else 3 * n + 1

/-- An orbit of `collatz` starting from `n` attains a value strictly below `f n`. -/
def AttainsBelow (f : ℕ → ℕ) (n : ℕ) : Prop :=
  ∃ k : ℕ, (collatz^[k]) n < f n

noncomputable def logWeightSum (S : Set ℕ) (N : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ Finset.Icc (1 : ℕ) N, (if n ∈ S then (1 / (n : ℝ)) else 0)

/-- A set `S` has logarithmic density zero if `(1/log N) * ∑_{n≤N, n∈S} (1/n) → 0`. -/
noncomputable def LogDensityZero (S : Set ℕ) : Prop :=
  Tendsto (fun N : ℕ => (1 / Real.log (N : ℝ)) * logWeightSum S N) atTop (nhds 0)

/-- **Almost all Collatz orbits attain almost bounded values** (Tao): for any function `f(n) → ∞`,
logarithmically almost every starting value has some iterate below `f n`. -/
theorem MainTheorem :
    ∀ f : ℕ → ℕ, Tendsto f atTop atTop →
      LogDensityZero {n : ℕ | ¬ AttainsBelow f n} := by
  sorry

end CollatzMapAlmostBoundedValues

