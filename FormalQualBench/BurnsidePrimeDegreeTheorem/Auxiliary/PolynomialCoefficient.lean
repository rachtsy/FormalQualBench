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

/--
The analogous binomial expansion for the translated powers appearing on the right-hand side of
the Schur--Müller polynomial identity.
-/
lemma sum_power_taylor_sub
    {F : Type*} [Field F] (f : F[X]) (U : Finset F) (w : ℕ) :
    (∑ u ∈ U, ((f + C u) ^ w - f ^ w)) =
      ∑ k ∈ Finset.range w,
        C ((w.choose (k + 1) : F) * ∑ u ∈ U, u ^ (k + 1)) *
          f ^ (w - (k + 1)) := by
  classical
  have hexpand (u : F) :
      (f + C u) ^ w - f ^ w =
        ∑ k ∈ Finset.range w,
          C ((w.choose (k + 1) : F) * u ^ (k + 1)) * f ^ (w - (k + 1)) := by
    rw [add_comm, add_pow, Finset.sum_range_succ']
    simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero]
    ring_nf
    apply Finset.sum_congr rfl
    intro k hk
    simp only [← C_pow, ← C_eq_natCast, ← C_mul]
    simp [mul_comm, mul_left_comm]
  rw [Finset.sum_congr rfl (fun u _ ↦ hexpand u)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_mul]
  rw [← map_sum]
  congr 2
  rw [← Finset.mul_sum]

/--
If the first `m` positive power sums of a nonempty finite set of nonzero field elements vanish,
then the set has more than `m` elements. This is the Vandermonde step in the Schur--Müller proof.
-/
lemma card_gt_of_power_sums_eq_zero
    {F : Type*} [Field F] (U : Finset F) (m : ℕ)
    (hU0 : 0 ∉ U) (hU : U.Nonempty)
    (hpow : ∀ k, 1 ≤ k → k ≤ m → (∑ u ∈ U, u ^ k) = 0) :
    m < U.card := by
  by_contra hm
  have hcard : U.card ≤ m := Nat.le_of_not_gt hm
  let e : Fin U.card ≃ U := U.equivFin.symm
  let f : Fin U.card → F := fun i ↦ (e i : U).1
  have hf : Function.Injective f := by
    intro i j hij
    apply e.injective
    exact Subtype.ext hij
  have hfv : ∀ i : Fin U.card, (∑ j : Fin U.card, f j * f j ^ (i : ℕ)) = 0 := by
    intro i
    simp_rw [← pow_succ']
    change (∑ j : Fin U.card, ((e j : U).1 : F) ^ ((i : ℕ) + 1)) = 0
    rw [Fintype.sum_equiv e (fun j ↦ ((e j : U).1 : F) ^ ((i : ℕ) + 1))
      (fun u : U ↦ (u.1 : F) ^ ((i : ℕ) + 1)) (fun j ↦ rfl)]
    change (∑ u ∈ U.attach, (u.1 : F) ^ ((i : ℕ) + 1)) = 0
    exact (Finset.sum_attach U (fun u ↦ u ^ ((i : ℕ) + 1))).trans
      (hpow ((i : ℕ) + 1) (by omega) (by omega))
  have hz := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf hfv
  have i : Fin U.card := ⟨0, hU.card_pos⟩
  have hi := congr_fun hz i
  have hfi : f i ≠ 0 := by
    intro h
    apply hU0
    have hei : (e i : F) ∈ U := (e i).2
    simpa [f, h] using hei
  exact hfi (by simpa using hi)

end BurnsidePrimeDegreeTheorem
