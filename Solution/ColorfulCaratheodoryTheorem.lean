import Mathlib

namespace ColorfulCaratheodoryTheorem

noncomputable section

open scoped BigOperators RealInnerProductSpace
open Set

lemma inner_ge_of_min_on_convex {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {S : Set V} (hS : Convex ℝ S) {p : V} (hp : p ∈ S)
    (hmin : ∀ q ∈ S, ‖p‖ ^ 2 ≤ ‖q‖ ^ 2)
    {q : V} (hq : q ∈ S) : ‖p‖ ^ 2 ≤ @inner ℝ V _ p q := by
  by_contra hn
  have hlt : @inner ℝ V _ p q < ‖p‖ ^ 2 := lt_of_not_ge hn
  let δ : ℝ := ‖p‖ ^ 2 - @inner ℝ V _ p q
  have hδ : 0 < δ := sub_pos.mpr hlt
  let M : ℝ := ‖q - p‖ ^ 2
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  let t : ℝ := min 1 (δ / (M + 1))
  have hden : 0 < M + 1 := by linarith
  have hrat : 0 < δ / (M + 1) := div_pos hδ hden
  have htpos : 0 < t := by
    dsimp [t]
    exact lt_min (by norm_num) hrat
  have ht1 : t ≤ (1 : ℝ) := by
    dsimp [t]
    exact min_le_left _ _
  have htrat : t ≤ δ / (M + 1) := by
    dsimp [t]
    exact min_le_right _ _
  have ht0 : 0 ≤ t := le_of_lt htpos
  have htM : t * M < 2 * δ := by
    have hle : t * (M + 1) ≤ δ := (le_div_iff₀ hden).mp htrat
    have hlt' : t * M < δ := by nlinarith
    nlinarith
  let z : V := (1 - t) • p + t • q
  have hz : z ∈ S := hS hp hq (sub_nonneg.mpr ht1) ht0 (by ring)
  have hbad : ‖z‖ ^ 2 < ‖p‖ ^ 2 := by
    have hz' : z = p + t • (q - p) := by
      dsimp [z]
      module
    rw [hz', norm_add_sq_real]
    have hi : @inner ℝ V _ p (t • (q - p)) =
        t * (@inner ℝ V _ p q - @inner ℝ V _ p p) := by
      rw [inner_smul_right, inner_sub_right]
    have hnrm : ‖t • (q - p)‖ ^ 2 = t ^ 2 * M := by
      rw [norm_smul]
      have habs : |t| = t := abs_of_pos htpos
      dsimp [Real.norm_eq_abs]
      rw [habs]
      dsimp [M]
      ring
    rw [hi, hnrm, real_inner_self_eq_norm_sq p]
    dsimp [δ] at htM ⊢
    nlinarith
  exact (not_lt_of_ge (hmin z hz)) hbad

theorem finite_colorful_zero {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (C : ι → Set V) (hfinite : ∀ i, (C i).Finite)
    (hcard : Fintype.card ι = Module.finrank ℝ V + 1)
    (hzero : ∀ i, (0 : V) ∈ convexHull ℝ (C i)) :
    ∃ p : ι → V, (∀ i, p i ∈ C i) ∧ (0 : V) ∈ convexHull ℝ (Set.range p) := by
  classical
  have hCne : ∀ i, (C i).Nonempty := by
    intro i
    rw [← @convexHull_nonempty_iff ℝ V _ _ _ _]
    exact ⟨0, hzero i⟩
  let κ (i : ι) := C i
  letI (i : ι) : Fintype (κ i) := (hfinite i).fintype
  letI (i : ι) : Nonempty (κ i) := (hCne i).to_subtype
  let S (g : ∀ i, κ i) : Set V := convexHull ℝ (Set.range fun i ↦ (g i : V))
  let U : Set V := ⋃ g : ∀ i, κ i, S g
  have hcomp : IsCompact U := by
    dsimp [U]
    apply isCompact_iUnion
    intro g
    exact (Set.finite_range _).isCompact_convexHull
  have hne : U.Nonempty := by
    let g : ∀ i, κ i := fun i ↦ Classical.choice (hCne i).to_subtype
    let i : ι := Classical.choice ‹Nonempty ι›
    have hx : (g i : V) ∈ S g := by
      dsimp [S]
      exact subset_convexHull ℝ _ (Set.mem_range_self _)
    exact ⟨_, Set.mem_iUnion.mpr ⟨g, hx⟩⟩
  obtain ⟨p, hpU, hpmin⟩ := hcomp.exists_isMinOn hne
    ((continuous_norm.pow 2).continuousOn)
  rcases Set.mem_iUnion.mp hpU with ⟨g, hp⟩
  by_contra hcontra
  have hp0 : p ≠ (0 : V) := by
    intro hpz
    apply hcontra
    refine ⟨fun i ↦ g i, fun i ↦ (g i).property, ?_⟩
    simpa [hpz] using hp
  let c : ℝ := ‖p‖ ^ 2
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hminS : ∀ z ∈ S g, ‖p‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    intro z hz
    exact hpmin (Set.mem_iUnion.mpr ⟨g, hz⟩)
  have hsupport : ∀ z ∈ S g, c ≤ @inner ℝ V _ p z := by
    intro z hz
    dsimp [c]
    exact inner_ge_of_min_on_convex (convex_convexHull ℝ _) hp hminS hz
  obtain ⟨α, hαfin, z, w, hzS, hzaff, hwpos, hwsum, hwbar⟩ :=
    eq_pos_convex_span_of_mem_convexHull hp
  letI : Fintype α := hαfin
  have hfind : ∀ a : α, ∃ i : ι, z a = g i := by
    intro a
    rcases hzS (Set.mem_range_self a) with ⟨i, hi⟩
    exact ⟨i, hi.symm⟩
  choose col hcol using hfind
  have hzinner : ∀ a : α, @inner ℝ V _ p (z a) = c := by
    intro a
    have hge : ∀ b : α, c ≤ @inner ℝ V _ p (z b) := by
      intro b
      exact hsupport _ (subset_convexHull ℝ _ <| hzS <| Set.mem_range_self b)
    have hsuminner : (∑ b : α, w b * @inner ℝ V _ p (z b)) = c := by
      have H := congrArg (fun u : V ↦ @inner ℝ V _ p u) hwbar
      simpa [inner_sum, inner_smul_right, c, real_inner_self_eq_norm_sq] using H
    by_contra hne'
    have hgt : c < @inner ℝ V _ p (z a) :=
      lt_of_le_of_ne (hge a) (Ne.symm hne')
    have hnonneg : ∀ b : α, 0 ≤ w b * (@inner ℝ V _ p (z b) - c) := by
      intro b
      exact mul_nonneg (le_of_lt (hwpos b)) (sub_nonneg.mpr (hge b))
    have hstrict : 0 < w a * (@inner ℝ V _ p (z a) - c) :=
      mul_pos (hwpos a) (sub_pos.mpr hgt)
    have hspos : 0 < ∑ b : α, w b * (@inner ℝ V _ p (z b) - c) :=
      Finset.sum_pos' (fun i _ ↦ hnonneg i) ⟨a, Finset.mem_univ _, hstrict⟩
    have hs0 : (∑ b : α, w b * (@inner ℝ V _ p (z b) - c)) = 0 := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsuminner, hwsum]
      ring
    exact (ne_of_gt hspos) hs0
  let L : V →ₗ[ℝ] ℝ := ((innerSL ℝ : V →L⋆[ℝ] V →L[ℝ] ℝ) p).toLinearMap
  have hL (v : V) : L v = @inner ℝ V _ p v := rfl
  let H : AffineSubspace ℝ V := AffineSubspace.mk' p (LinearMap.ker L)
  have hzin : Set.range z ⊆ (H : Set V) := by
    rintro _ ⟨a, rfl⟩
    change z a ∈ AffineSubspace.mk' p (LinearMap.ker L)
    rw [AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.mem_ker]
    rw [LinearMap.map_sub, hL, hL, hzinner a, real_inner_self_eq_norm_sq]
    simp [c]
  have hlecard : Fintype.card α ≤ Module.finrank ℝ V + 1 := by
    calc
      Fintype.card α ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range z)) + 1 :=
        hzaff.card_le_finrank_succ
      _ ≤ Module.finrank ℝ V + 1 :=
        Nat.add_le_add_right (Submodule.finrank_le _) _
  have hnecard : Fintype.card α ≠ Module.finrank ℝ V + 1 := by
    intro heq
    have htop : affineSpan ℝ (Set.range z) = (⊤ : AffineSubspace ℝ V) :=
      hzaff.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr heq
    have hsub : (⊤ : AffineSubspace ℝ V) ≤ H := by
      rw [← htop]
      exact (affineSpan_le).2 hzin
    have h0mem : (0 : V) ∈ H := hsub (AffineSubspace.mem_top ℝ V 0)
    change (0 : V) ∈ AffineSubspace.mk' p (LinearMap.ker L) at h0mem
    have hzker : L (0 - p) = 0 := by
      simpa [AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.mem_ker] using h0mem
    have : c = 0 := by
      simpa [LinearMap.map_sub, hL, c, real_inner_self_eq_norm_sq] using hzker
    exact (ne_of_gt hc) this
  have hltα : Fintype.card α < Fintype.card ι := by
    rw [hcard]
    exact lt_of_le_of_ne hlecard hnecard
  have hnotsurj : ¬Function.Surjective col := by
    intro hs
    exact (not_le_of_gt hltα) (Fintype.card_le_of_surjective col hs)
  simp only [Function.Surjective] at hnotsurj
  push_neg at hnotsurj
  rcases hnotsurj with ⟨k, hk⟩
  have hxchoice : ∃ b : κ k, @inner ℝ V _ p (b : V) ≤ 0 := by
    by_contra hh
    push_neg at hh
    let T : Set V := {v | 0 < @inner ℝ V _ p v}
    have hTconv : Convex ℝ T := by
      intro u hu v hv a b ha hb hab
      change 0 < @inner ℝ V _ p (a • u + b • v)
      have hu' : 0 < @inner ℝ V _ p u := hu
      have hv' : 0 < @inner ℝ V _ p v := hv
      rw [inner_add_right, inner_smul_right, inner_smul_right]
      rcases eq_or_ne a 0 with ha0 | ha0
      · subst a
        have hb1 : b = 1 := by linarith
        subst b
        simpa only [zero_mul, zero_add, one_mul] using hv'
      · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        exact add_pos_of_pos_of_nonneg (mul_pos ha' hu') (mul_nonneg hb hv'.le)
    have hCT : C k ⊆ T := by
      intro x hx
      exact hh ⟨x, hx⟩
    have hhull : convexHull ℝ (C k) ⊆ T := convexHull_min hCT hTconv
    have hzT := hhull (hzero k)
    change (0 : ℝ) < @inner ℝ V _ p (0 : V) at hzT
    simp at hzT
  rcases hxchoice with ⟨b, hb⟩
  let g' : ∀ i, κ i := fun i ↦ if h : i = k then h ▸ b else g i
  have hgcol (a : α) : g' (col a) = g (col a) := by
    dsimp [g']
    split_ifs with h
    · exact False.elim ((hk a) h)
    · rfl
  have hza : ∀ a : α, z a ∈ S g' := by
    intro a
    dsimp [S]
    apply subset_convexHull ℝ _
    refine ⟨col a, ?_⟩
    change (g' (col a) : V) = z a
    rw [hgcol a]
    exact (hcol a).symm
  have hp' : p ∈ S g' := by
    have hs := (convex_convexHull ℝ (Set.range fun i ↦ (g' i : V))).sum_mem
      (t := Finset.univ) (w := w) (z := z)
      (fun i _ ↦ (hwpos i).le) hwsum (fun i _ ↦ hza i)
    simpa [hwbar] using hs
  have hxb : (b : V) ∈ S g' := by
    dsimp [S]
    apply subset_convexHull ℝ _
    refine ⟨k, ?_⟩
    simp [g']
  have hmin' : ∀ y ∈ S g', ‖p‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    intro y hy
    exact hpmin (Set.mem_iUnion.mpr ⟨g', hy⟩)
  have hge' : c ≤ @inner ℝ V _ p (b : V) := by
    dsimp [c]
    exact inner_ge_of_min_on_convex (convex_convexHull ℝ _) hp' hmin' hxb
  linarith

/-- The colorful Carathéodory theorem (statement): if each of `d+1` sets of points in `ℝ^d`
contains the origin in its convex hull, then one can pick one point from each set so that the
origin lies in the convex hull of the chosen points. -/
theorem MainTheorem (d : ℕ)
    (C : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)))
    (hC : ∀ i, (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (C i)) :
    ∃ p : Fin (d + 1) → EuclideanSpace ℝ (Fin d),
      (∀ i, p i ∈ C i) ∧ (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (Set.range p) := by
  let D (i : Fin (d + 1)) : Set (EuclideanSpace ℝ (Fin d)) :=
    ↑(Caratheodory.minCardFinsetOfMemConvexHull (hC i))
  have hDC : ∀ i, D i ⊆ C i :=
    fun i ↦ Caratheodory.minCardFinsetOfMemConvexHull_subseteq (hC i)
  have hDfinite : ∀ i, (D i).Finite :=
    fun i ↦ Finset.finite_toSet _
  have hDzero : ∀ i, (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (D i) :=
    fun i ↦ Caratheodory.mem_minCardFinsetOfMemConvexHull (hC i)
  obtain ⟨p, hpD, hp0⟩ := finite_colorful_zero D hDfinite (by simp) hDzero
  exact ⟨p, fun i ↦ hDC i (hpD i), hp0⟩

end

end ColorfulCaratheodoryTheorem
