import Mathlib

namespace BurnsidePrimeDegreeTheorem

open scoped BigOperators
open Polynomial

/--
The first potentially nonzero power sum controls the corresponding top coefficient of the sum of
the translated polynomial differences.
-/
lemma coeff_sum_taylor_sub
    {F : Type*} [Field F]
    (g : F[X]) (U : Finset F) (r : ℕ) (hr0 : 0 < r)
    (hr : r ≤ g.natDegree)
    (hpow : ∀ k, 1 ≤ k → k < r → (∑ u ∈ U, u ^ k) = 0) :
    (∑ u ∈ U, (g.taylor u - g)).coeff (g.natDegree - r) =
      g.leadingCoeff * (g.natDegree.choose r : F) * (∑ u ∈ U, u ^ r) := by
  classical
  let d := g.natDegree
  let n := d - r
  let H := g.hasseDeriv n
  have hdn : d - n = r := by
    dsimp [n]
    exact Nat.sub_sub_self hr
  have hHdeg : H.natDegree ≤ r := by
    dsimp [H]
    exact (Polynomial.natDegree_hasseDeriv_le g n).trans_eq hdn
  have hterm (u : F) :
      (g.taylor u - g).coeff n =
        ∑ k ∈ Finset.range r, H.coeff (k + 1) * u ^ (k + 1) := by
    rw [coeff_sub, Polynomial.taylor_coeff]
    change H.eval u - g.coeff n = _
    rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt hHdeg (Nat.lt_succ_self r))]
    rw [Finset.sum_range_succ']
    simp only [pow_zero, mul_one]
    have hH0 : H.coeff 0 = g.coeff n := by
      simp [H, Polynomial.hasseDeriv_coeff]
    rw [hH0]
    ring
  rw [Polynomial.finset_sum_coeff]
  change (∑ u ∈ U, (g.taylor u - g).coeff n) = _
  rw [Finset.sum_congr rfl (fun u _ ↦ hterm u)]
  rw [Finset.sum_comm]
  have hlower :
      (∑ k ∈ Finset.range (r - 1),
        ∑ u ∈ U, H.coeff (k + 1) * u ^ (k + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_range] at hk
    rw [← Finset.mul_sum]
    rw [hpow (k + 1) (by omega) (by omega), mul_zero]
  have hrpred : r.pred = r - 1 := rfl
  rw [← Nat.succ_pred_eq_of_pos hr0, Finset.sum_range_succ]
  rw [hrpred, hlower, zero_add]
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hr0.ne')]
  rw [← Finset.mul_sum]
  have hcoeff : H.coeff r = g.leadingCoeff * (d.choose r : F) := by
    simp only [H, Polynomial.hasseDeriv_coeff]
    have hnr : r + n = d := by
      dsimp [n]
      omega
    rw [hnr, coeff_natDegree]
    rw [Nat.choose_symm_of_eq_add hnr.symm]
    ring
  rw [hcoeff]
  have hpredsucc : (r - 1).succ = r := by omega
  rw [hpredsucc]

end BurnsidePrimeDegreeTheorem
