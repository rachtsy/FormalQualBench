import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat

namespace ParisHarringtonPrinciple

open Finset

/-- A subset `H` of `[1, N]` is relatively large for the Paris-Harrington principle if it has at
least `m` elements and its cardinality is at least its minimum element. -/
def RelativelyLarge (m N : ℕ) (H : Finset ℕ) : Prop :=
  H ⊆ Finset.Ico 1 (N + 1) ∧
  m ≤ H.card ∧
  ∃ hne : H.Nonempty, H.min' hne ≤ H.card

/-- A set `H` is homogeneous for a coloring if all `k`-subsets of `H` have the same color. -/
def IsHomogeneous {α β : Type*} [DecidableEq α] (k : ℕ) (H : Finset α)
    (c : Finset α → β) : Prop :=
  ∀ s ∈ H.powersetCard k, ∀ t ∈ H.powersetCard k, c s = c t

/-- Paris-Harrington principle (strengthened finite Ramsey theorem): assuming `0 < r` and `k ≤ m`,
there exists `N` such that every `r`-coloring of the `k`-subsets of `[1, N]` has a relatively
large homogeneous set. This is the finite combinatorial statement whose unprovability over Peano
arithmetic is usually called the Paris-Harrington theorem. -/
theorem MainTheorem (k r m : ℕ) (hr : 0 < r) (hm : k ≤ m) :
    ∃ N : ℕ, ∀ (c : Finset ℕ → Fin r),
      ∃ H : Finset ℕ, RelativelyLarge m N H ∧ IsHomogeneous k H c := by
  sorry

end ParisHarringtonPrinciple
