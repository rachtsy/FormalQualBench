import Mathlib
import FormalQualBench.BurnsidePrimeDegreeTheorem.Auxiliary.PolynomialCoefficient

namespace BurnsidePrimeDegreeTheorem

open scoped BigOperators
open Polynomial

lemma affine_of_difference_set_preserving
    {p : ℕ} (hp : p.Prime)
    (U : Finset (ZMod p))
    (hU0 : 0 ∉ U) (hU : U.Nonempty)
    (hUcard : 2 * U.card ≤ p - 1)
    (π : Equiv.Perm (ZMod p))
    (hpres : ∀ i j : ZMod p, i - j ∈ U → π i - π j ∈ U) :
    ∃ a b : ZMod p, a ≠ 0 ∧ ∀ i, π i = a * i + b := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hφinj (i : ZMod p) : Function.Injective (fun u : ZMod p ↦ π (i + u) - π i) := by
    intro u v huv
    apply add_left_cancel (a := π i)
    simpa [sub_eq_iff_eq_add] using huv
  have himage (i : ZMod p) :
      U.image (fun u : ZMod p ↦ π (i + u) - π i) = U := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      apply hpres (i + u) i
      simpa using hu
    · rw [Finset.card_image_of_injective _ (hφinj i)]
  have hpowsum (i : ZMod p) (w : ℕ) :
      (∑ u ∈ U, π (i + u) ^ w) = ∑ u ∈ U, (π i + u) ^ w := by
    calc
      (∑ u ∈ U, π (i + u) ^ w) =
          ∑ u ∈ U, (π i + (π (i + u) - π i)) ^ w := by
            apply Finset.sum_congr rfl
            intro u hu
            congr 1
            ring
      _ = ∑ v ∈ U.image (fun u : ZMod p ↦ π (i + u) - π i), (π i + v) ^ w := by
            rw [Finset.sum_image]
            intro u hu v hv huv
            exact hφinj i huv
      _ = ∑ u ∈ U, (π i + u) ^ w := by rw [himage]
  let f : (ZMod p)[X] := (Lagrange.interpolate Finset.univ id) π
  have hfeval (i : ZMod p) : f.eval i = π i := by
    simpa [f] using
      (Lagrange.eval_interpolate_at_node (s := (Finset.univ : Finset (ZMod p)))
        (v := id) π (Set.injOn_id _) (Finset.mem_univ i))
  have hf0 : f ≠ 0 := by
    intro hf
    apply (zero_ne_one : (0 : ZMod p) ≠ 1)
    apply π.injective
    rw [← hfeval 0, ← hfeval 1, hf]
    simp
  have hfdeg : f.natDegree < p := by
    rw [Polynomial.natDegree_lt_iff_degree_lt hf0]
    simpa [f] using
      (Lagrange.degree_interpolate_lt π
        (show Set.InjOn (id : ZMod p → ZMod p) (↑(Finset.univ : Finset (ZMod p))) from
          Set.injOn_id _))
  let n := f.natDegree
  have hnlt : n < p := hfdeg
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hn0
    have h01 : (0 : ZMod p) ≠ 1 := zero_ne_one
    apply h01
    apply π.injective
    rw [← hfeval 0, ← hfeval 1, ← hc]
    simp
  have hexists :
      ∃ r : ℕ, 1 ≤ r ∧ r ≤ U.card ∧ (∑ u ∈ U, u ^ r) ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : ∀ k, 1 ≤ k → k ≤ U.card → (∑ u ∈ U, u ^ k) = 0 := by
      intro k hk1 hkU
      exact h k hk1 hkU
    have := card_gt_of_power_sums_eq_zero U U.card hU0 hU hz
    omega
  let r := Nat.find hexists
  have hr := Nat.find_spec hexists
  have hrpos : 0 < r := hr.1
  have hrU : r ≤ U.card := hr.2.1
  have hrne : (∑ u ∈ U, u ^ r) ≠ 0 := hr.2.2
  have hlower : ∀ k, 1 ≤ k → k < r → (∑ u ∈ U, u ^ k) = 0 := by
    intro k hk1 hkr
    by_contra hkne
    have hkU : k ≤ U.card := (Nat.le_of_lt hkr).trans hrU
    have hfind : r ≤ k := Nat.find_min' hexists ⟨hk1, hkU, hkne⟩
    omega
  let w := (p - 1) / n
  have hnle : n ≤ p - 1 := by omega
  have hwpos : 0 < w := by
    dsimp [w]
    exact Nat.div_pos hnle hnpos
  have hnw : n * w ≤ p - 1 := by
    dsimp [w]
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self (p - 1) n
  have hmax : p - 1 < n * (w + 1) := by
    dsimp [w]
    exact Nat.lt_mul_div_succ (p - 1) hnpos
  have hrnw : r ≤ n * w := by
    have htwor : 2 * r ≤ p - 1 := by
      exact (Nat.mul_le_mul_left 2 hrU).trans hUcard
    have htwo : n * (w + 1) ≤ 2 * (n * w) := by
      calc
        n * (w + 1) ≤ n * (2 * w) := Nat.mul_le_mul_left n (by omega)
        _ = 2 * (n * w) := by ring
    omega
  let lhs : (ZMod p)[X] := ∑ u ∈ U, ((f.taylor u) ^ w - f ^ w)
  let rhs : (ZMod p)[X] := ∑ u ∈ U, ((f + C u) ^ w - f ^ w)
  have hlhsdeg : lhs.natDegree ≤ n * w := by
    dsimp [lhs]
    refine Polynomial.natDegree_sum_le_of_forall_le U
      (fun u ↦ (f.taylor u) ^ w - f ^ w) ?_
    intro u hu
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    simp [Polynomial.natDegree_pow, n, Nat.mul_comm]
  have hrhsdeg : rhs.natDegree ≤ n * w := by
    dsimp [rhs]
    refine Polynomial.natDegree_sum_le_of_forall_le U
      (fun u ↦ (f + C u) ^ w - f ^ w) ?_
    intro u hu
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    have hadd : (f + C u).natDegree ≤ n := by
      refine (Polynomial.natDegree_add_le _ _).trans ?_
      simp [n]
    have hpw : ((f + C u) ^ w).natDegree ≤ n * w := by
      rw [Polynomial.natDegree_pow]
      nlinarith
    rw [max_le_iff]
    constructor
    · exact hpw
    · simp [Polynomial.natDegree_pow, n, Nat.mul_comm]
  have hpoly : lhs = rhs := by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq lhs rhs (f := id)
    · exact Function.injective_id
    · intro i
      dsimp [lhs, rhs]
      simp only [Polynomial.eval_finset_sum, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.taylor_eval, Polynomial.eval_add, Polynomial.eval_C]
      simpa [hfeval] using hpowsum i w
    · rw [ZMod.card]
      exact lt_of_le_of_lt (max_le hlhsdeg hrhsdeg) (by omega)
  have hlhsform :
      lhs = ∑ u ∈ U, ((f ^ w).taylor u - f ^ w) := by
    dsimp [lhs]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Polynomial.taylor_pow]
  have hpowdeg : (f ^ w).natDegree = n * w := by
    rw [Polynomial.natDegree_pow]
    simp [n, Nat.mul_comm]
  have hcoeffL :
      lhs.coeff (n * w - r) =
        (f ^ w).leadingCoeff * ((n * w).choose r : ZMod p) *
          (∑ u ∈ U, u ^ r) := by
    rw [hlhsform]
    have h := coeff_sum_taylor_sub (g := f ^ w) U r hrpos
      (by simpa [hpowdeg] using hrnw) hlower
    rw [hpowdeg] at h
    exact h
  have hrhsform :
      rhs = ∑ k ∈ Finset.range w,
        C ((w.choose (k + 1) : ZMod p) * ∑ u ∈ U, u ^ (k + 1)) *
          f ^ (w - (k + 1)) := by
    dsimp [rhs]
    exact sum_power_taylor_sub f U w
  have hn1 : n = 1 := by
    by_contra hnne
    have hn2 : 2 ≤ n := by omega
    have hcoeffR : rhs.coeff (n * w - r) = 0 := by
      rw [hrhsform, Polynomial.finset_sum_coeff]
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_range] at hk
      by_cases hkr : k + 1 < r
      · rw [hlower (k + 1) (by omega) hkr]
        simp
      · have hrk : r ≤ k + 1 := by omega
        have hkw : k + 1 ≤ w := by omega
        have hrw : r ≤ w := hrk.trans hkw
        let A : ZMod p := (w.choose (k + 1) : ZMod p) * ∑ u ∈ U, u ^ (k + 1)
        have htermdeg :
            (C A * f ^ (w - (k + 1))).natDegree ≤ n * (w - (k + 1)) := by
          calc
            _ ≤ (C A).natDegree + (f ^ (w - (k + 1))).natDegree :=
              Polynomial.natDegree_mul_le
            _ = n * (w - (k + 1)) := by
              simp [Polynomial.natDegree_pow, n, Nat.mul_comm]
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        refine htermdeg.trans_lt ?_
        have hsub : w - (k + 1) ≤ w - r := Nat.sub_le_sub_left hrk w
        have hmul : n * (w - (k + 1)) ≤ n * (w - r) := Nat.mul_le_mul_left n hsub
        refine hmul.trans_lt ?_
        rw [Nat.mul_sub_left_distrib]
        have hnr : r < n * r := by nlinarith
        have hrnwlt : r < n * w := lt_of_le_of_lt hrw (by nlinarith)
        exact Nat.sub_lt_sub_left hrnwlt hnr
    have hcoeffEq : lhs.coeff (n * w - r) = rhs.coeff (n * w - r) := by rw [hpoly]
    rw [hcoeffL, hcoeffR] at hcoeffEq
    have hlead : (f ^ w).leadingCoeff ≠ 0 := by
      rw [Polynomial.leadingCoeff_pow]
      exact pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hf0)
    have hchooseNat : ¬ p ∣ (n * w).choose r := by
      intro hdvd
      exact (hp.dvd_iff_not_coprime.mp hdvd)
        (hp.coprime_choose_of_lt (by omega) hrnw)
    have hchoose : ((n * w).choose r : ZMod p) ≠ 0 := by
      intro hzero
      have : p ∣ (n * w).choose r :=
        (ZMod.natCast_eq_zero_iff ((n * w).choose r) p).mp hzero
      exact hchooseNat this
    rcases mul_eq_zero.mp hcoeffEq with hzero | hzero
    · rcases mul_eq_zero.mp hzero with hzero | hzero
      · exact hlead hzero
      · exact hchoose hzero
    · exact hrne hzero
  have hfdeg1 : f.natDegree = 1 := by simpa [n] using hn1
  obtain ⟨a, ha, b, hab⟩ := Polynomial.natDegree_eq_one.mp hfdeg1
  refine ⟨a, b, ha, fun i ↦ ?_⟩
  rw [← hfeval i, ← hab]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

end BurnsidePrimeDegreeTheorem

namespace BurnsidePrimeDegreeTheorem

lemma affine_of_difference_set_preserving'
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (U : Finset (ZMod p))
    (hU0 : 0 ∉ U) (hU : U.Nonempty)
    (hUsub : U ⊆ Finset.univ.erase 0)
    (hUproper : U.card < p - 1)
    (π : Equiv.Perm (ZMod p))
    (hpres : ∀ i j : ZMod p, i - j ∈ U → π i - π j ∈ U) :
    ∃ a b : ZMod p, a ≠ 0 ∧ ∀ i, π i = a * i + b := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hφinj (i : ZMod p) : Function.Injective (fun u : ZMod p ↦ π (i + u) - π i) := by
    intro u v huv
    apply add_left_cancel (a := π i)
    simpa [sub_eq_iff_eq_add] using huv
  have himage (i : ZMod p) :
      U.image (fun u : ZMod p ↦ π (i + u) - π i) = U := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      apply hpres (i + u) i
      simpa using hu
    · rw [Finset.card_image_of_injective _ (hφinj i)]
  have hiff (i j : ZMod p) : i - j ∈ U ↔ π i - π j ∈ U := by
    constructor
    · exact hpres i j
    · intro hout
      have hout' : π (j + (i - j)) - π j ∈ U := by simpa using hout
      rw [← himage j] at hout'
      obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hout'
      have hud : u = i - j := hφinj j (by simpa using heq)
      simpa [hud] using hu
  by_cases hsmall : 2 * U.card ≤ p - 1
  · exact affine_of_difference_set_preserving hp U hU0 hU hsmall π hpres
  · let S : Finset (ZMod p) := Finset.univ.erase 0
    let V : Finset (ZMod p) := S \ U
    have hScard : S.card = p - 1 := by
      dsimp [S]
      rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)), Finset.card_univ, ZMod.card]
    have hVcard : V.card = p - 1 - U.card := by
      dsimp [V]
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hUsub, hScard]
    have hVsmall : 2 * V.card ≤ p - 1 := by
      rw [hVcard]
      omega
    have hV0 : 0 ∉ V := by simp [V, S]
    have hV : V.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      have : V.card = 0 := by rw [h]; simp
      rw [hVcard] at this
      omega
    have hVpres : ∀ i j : ZMod p, i - j ∈ V → π i - π j ∈ V := by
      intro i j hij
      have hdS : i - j ∈ S := (Finset.mem_sdiff.mp hij).1
      have hdU : i - j ∉ U := (Finset.mem_sdiff.mp hij).2
      have hijne : i ≠ j := by
        intro heq
        subst j
        exact hV0 (by simpa using hij)
      have hout0 : π i - π j ≠ 0 := sub_ne_zero.mpr (π.injective.ne hijne)
      apply Finset.mem_sdiff.mpr
      constructor
      · simp [S, hout0]
      · exact fun houtU ↦ hdU ((hiff i j).mpr houtU)
    exact affine_of_difference_set_preserving hp V hV0 hV hVsmall π hVpres

end BurnsidePrimeDegreeTheorem
