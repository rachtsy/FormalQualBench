import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
import Mathlib.Analysis.VonNeumannAlgebra.Basic

namespace VonNeumannDoubleCommutantTheorem

open scoped Topology InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
noncomputable section
private theorem closure_invt {f : H →L[ℂ] H} {s : Submodule ℂ H}
    (hs : s ∈ Module.End.invtSubmodule f.toLinearMap) :
    s.topologicalClosure ∈ Module.End.invtSubmodule f.toLinearMap := by
  rw [Module.End.mem_invtSubmodule_iff_map_le] at hs ⊢
  exact (s.topologicalClosure_map f).trans (Submodule.topologicalClosure_mono hs)
private theorem orthogonal_invt (K : Submodule ℂ H) {a : H →L[ℂ] H}
    (hK : K ∈ Module.End.invtSubmodule (star a).toLinearMap) :
    Kᗮ ∈ Module.End.invtSubmodule a.toLinearMap := by
  rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at hK ⊢
  intro v hv
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  calc
    ⟪u, a v⟫_ℂ = ⟪(ContinuousLinearMap.adjoint a) u, v⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_left a v u).symm
    _ = 0 := by
      simpa [ContinuousLinearMap.star_eq_adjoint] using hv (star a u) (hK u hu)
private abbrev HSum (H ι : Type*) := PiLp 2 (fun _ : ι ↦ H)
private def diag {ι : Type*} [Fintype ι] (a : H →L[ℂ] H) : HSum H ι →L[ℂ] HSum H ι :=
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι ↦ H)
  e.symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i ↦ a ∘L ContinuousLinearMap.proj i) ∘L e.toContinuousLinearMap
@[simp] private lemma diag_apply {ι : Type*} [Fintype ι] (a : H →L[ℂ] H)
    (v : HSum H ι) (i : ι) : diag a v i = a (v i) := by simp [diag]
@[simp] private lemma diag_star {ι : Type*} [Fintype ι] (a : H →L[ℂ] H) :
    diag (ι := ι) (star a) = star (diag a) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  simp only [diag_apply, PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ ↦ ContinuousLinearMap.adjoint_inner_left a (w i) (v i)
private def single {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) : H →L[ℂ] HSum H ι :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι ↦ H)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℂ (fun _ : ι ↦ H) i
@[simp] private lemma single_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (v : H) : single i v j = if j = i then v else 0 := by
  by_cases h : j = i
  · subst j
    simp [single, Pi.single_eq_same]
  · simp [single, h, Pi.single_eq_of_ne]

@[simp] private lemma diag_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : H →L[ℂ] H) (j : ι) (v : H) : diag a (single j v) = single j (a v) := by
  ext i
  by_cases h : i = j <;> simp [h]

private def entry {ι : Type*} [Fintype ι] [DecidableEq ι] (z : HSum H ι →L[ℂ] HSum H ι)
    (i j : ι) : H →L[ℂ] H := PiLp.proj 2 (fun _ : ι ↦ H) i ∘L z ∘L single j

private lemma coord_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : HSum H ι →L[ℂ] HSum H ι) (i : ι) (v : HSum H ι) :
    z v i = ∑ j, entry z i j (v j) := by
  have hv : ∑ j, single j (v j) = v := by ext j; simp
  rw [← hv, map_sum]
  simp [entry]

private theorem finite_approx {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {x : H →L[ℂ] H}
    (hx : x ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) (ξ : HSum H ι) :
    diag x ξ ∈ closure ((fun a : H →L[ℂ] H ↦ diag a ξ) '' (S : Set (H →L[ℂ] H))) := by
  let ev : (H →L[ℂ] H) →ₗ[ℂ] HSum H ι :=
    { toFun := fun a ↦ diag a ξ
      map_add' := by intros; ext i; simp
      map_smul' := by intros; ext i; simp }
  let K0 := S.toSubalgebra.toSubmodule.map ev
  let K : Submodule ℂ (HSum H ι) := K0.topologicalClosure
  have hK0 : (K0 : Set (HSum H ι)) = (fun a : H →L[ℂ] H ↦ diag a ξ) '' S := by
    ext v
    constructor <;> rintro ⟨a, ha, rfl⟩ <;> exact ⟨a, ha, rfl⟩
  have hK {a : H →L[ℂ] H} (ha : a ∈ S) : K ∈ Module.End.invtSubmodule (diag a).toLinearMap := by
    apply closure_invt
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    rintro _ ⟨b, hb, rfl⟩
    refine ⟨a * b, S.mul_mem ha hb, ?_⟩
    ext i
    simp [ev, ContinuousLinearMap.mul_def]
  let p := K.starProjection
  have hp {a : H →L[ℂ] H} (ha : a ∈ S) : Commute p.toLinearMap (diag a).toLinearMap := by
    have ho : Kᗮ ∈ Module.End.invtSubmodule (diag a).toLinearMap := by
      apply orthogonal_invt K
      simpa using hK (star_mem ha)
    have hi : IsIdempotentElem p.toLinearMap :=
      ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mpr
        (Submodule.isIdempotentElem_starProjection (K := K))
    exact (LinearMap.IsIdempotentElem.commute_iff hi).2 <| by
      simpa [p, Submodule.range_starProjection, Submodule.ker_starProjection] using ⟨hK ha, ho⟩
  have he (i j : ι) : entry p i j ∈ Set.centralizer (S : Set (H →L[ℂ] H)) := by
    intro a ha
    ext v
    have h := congrArg (fun f : HSum H ι →ₗ[ℂ] HSum H ι ↦ f (single j v) i) (hp ha).eq
    simpa [entry, Module.End.mul_apply] using h.symm
  have hpx : Commute p.toLinearMap (diag x).toLinearMap := by
    rw [Commute]
    change p.toLinearMap.comp (diag x).toLinearMap = (diag x).toLinearMap.comp p.toLinearMap
    ext v i
    change p (diag x v) i = x (p v i)
    rw [coord_sum p i (diag x v), coord_sum p i v, map_sum]
    simp only [diag_apply]
    exact Finset.sum_congr rfl fun j _ ↦ by
      simpa [ContinuousLinearMap.mul_def] using
        congrArg (fun a : H →L[ℂ] H ↦ a (v j)) (hx _ (he i j))
  have hi : IsIdempotentElem p.toLinearMap :=
    ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mpr
      (Submodule.isIdempotentElem_starProjection (K := K))
  have hxK : K ∈ Module.End.invtSubmodule (diag x).toLinearMap := by
    simpa [p, Submodule.range_starProjection] using
      ((LinearMap.IsIdempotentElem.commute_iff hi).1 hpx).1
  have hξ : ξ ∈ K := Submodule.le_topologicalClosure K0 ⟨1, S.one_mem, by ext i; simp [ev]⟩
  have hxξ := (Module.End.mem_invtSubmodule (diag x).toLinearMap).1 hxK hξ
  change diag x ξ ∈ closure (K0 : Set (HSum H ι)) at hxξ
  rwa [hK0] at hxξ

private theorem wot_approx (S : StarSubalgebra ℂ (H →L[ℂ] H)) {x : H →L[ℂ] H}
    (hx : x ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    ContinuousLinearMap.toWOT (RingHom.id ℂ) H H x ∈
      closure (ContinuousLinearMap.toWOT (RingHom.id ℂ) H H '' (S : Set (H →L[ℂ] H))) := by
  classical
  let toWOT : (H →L[ℂ] H) → H →WOT[ℂ] H := ContinuousLinearMap.toWOT (RingHom.id ℂ) H H
  let p := ContinuousLinearMapWOT.seminormFamily (RingHom.id ℂ) H H
  have hp : WithSeminorms p := ContinuousLinearMapWOT.withSeminorms
  refine mem_closure_iff.2 fun U hU hxU ↦ ?_
  rcases (WithSeminorms.mem_nhds_iff hp (toWOT x) U).1 (hU.mem_nhds hxU) with ⟨s, r, hr, hs⟩
  let C : ℝ := s.sup (fun q : H × StrongDual ℂ H ↦ ‖q.2‖₊) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let ε := r / C
  have hε : 0 < ε := div_pos hr hC
  let ξ : HSum H s := WithLp.toLp 2 fun q : s ↦ q.1.1
  letI : DecidableEq s := Classical.decEq s
  rcases Metric.mem_closure_iff.1 (finite_approx S hx ξ) ε hε with ⟨_, ⟨a, ha, rfl⟩, hd⟩
  have hball : toWOT a ∈ (s.sup p).ball (toWOT x) r := by
    rw [Seminorm.ball_finset_sup_eq_iInter _ s _ hr]
    refine Set.mem_iInter₂.2 fun q hq ↦ ?_
    let qs : s := ⟨q, hq⟩
    have hv : ‖(a - x) q.1‖ < ε := by
      have hle := PiLp.dist_apply_le (x := diag x ξ) (y := diag a ξ) qs
      simpa [ξ, dist_eq_norm, ContinuousLinearMap.sub_apply, norm_sub_rev] using
        lt_of_le_of_lt hle hd
    have hn : ‖q.2‖ ≤ C := by
      have h : ‖q.2‖₊ ≤ s.sup (fun z : H × StrongDual ℂ H ↦ ‖z.2‖₊) :=
        Finset.le_sup (f := fun z : H × StrongDual ℂ H ↦ ‖z.2‖₊) hq
      have h' : ‖q.2‖ ≤ (s.sup fun z : H × StrongDual ℂ H ↦ ‖z.2‖₊ : NNReal) := by
        exact_mod_cast h
      dsimp [C]
      linarith
    have hCr : C * ε = r := by dsimp [ε]; field_simp [ne_of_gt hC]
    have hlt : ‖q.2 ((a - x) q.1)‖ < r := by
      refine lt_of_le_of_lt (q.2.le_opNorm _) ?_
      by_cases hq0 : ‖q.2‖ = 0
      · have hq : q.2 = 0 := by simpa using hq0
        simpa [hq] using hr
      · exact lt_of_lt_of_le
          (mul_lt_mul_of_pos_left hv (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hq0))) <|
            hCr ▸ mul_le_mul_of_nonneg_right hn hε.le
    rw [Seminorm.mem_ball]
    change ‖q.2 ((toWOT a - toWOT x) q.1)‖ < r
    simpa [toWOT, ContinuousLinearMapWOT.sub_apply, ContinuousLinearMap.sub_apply] using hlt
  exact ⟨toWOT a, hs hball, a, ha, rfl⟩

private theorem wot_centralizer_closed (T : Set (H →L[ℂ] H)) :
    IsClosed (ContinuousLinearMap.toWOT (RingHom.id ℂ) H H '' Set.centralizer T) := by
  let e := ContinuousLinearMap.toWOT (RingHom.id ℂ) H H
  have hs : e '' Set.centralizer T = ⋂ z ∈ T,
      {A : H →WOT[ℂ] H | e (z.comp (e.symm A)) = e ((e.symm A).comp z)} := by
    ext A
    constructor
    · rintro ⟨a, ha, rfl⟩
      simp only [Set.mem_iInter]
      intro z hz
      simpa [e, ContinuousLinearMap.mul_def] using congrArg e (ha z hz)
    · intro h
      refine ⟨e.symm A, ?_, by simp [e]⟩
      intro z hz
      simpa [e, ContinuousLinearMap.mul_def] using congrArg e.symm (Set.mem_iInter₂.mp h z hz)
  rw [hs]
  exact isClosed_biInter fun z _ ↦ isClosed_eq
    (ContinuousLinearMapWOT.continuous_of_dual_apply_continuous fun v y ↦ by
      simpa [e, ContinuousLinearMap.comp_apply] using
        ContinuousLinearMapWOT.continuous_dual_apply (x := v) (y := y.comp z))
    (ContinuousLinearMapWOT.continuous_of_dual_apply_continuous fun v y ↦ by
      simpa [e, ContinuousLinearMap.comp_apply] using
        ContinuousLinearMapWOT.continuous_dual_apply (x := z v) (y := y))

/-- **von Neumann double commutant theorem (statement)**:
for a unital *-subalgebra `S ⊆ B(H)`, being closed in the weak operator topology is equivalent to
being equal to its bicommutant. -/
theorem MainTheorem (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    IsClosed ((ContinuousLinearMap.toWOT (RingHom.id ℂ) H H) '' (S : Set (H →L[ℂ] H))) ↔
      Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) = (S : Set (H →L[ℂ] H)) := by
  constructor
  · intro h
    apply Set.Subset.antisymm
    · intro x hx
      have hx' := wot_approx S hx
      rw [h.closure_eq] at hx'
      rcases hx' with ⟨a, ha, hax⟩
      simpa [((ContinuousLinearMap.toWOT (RingHom.id ℂ) H H).injective hax).symm] using ha
    · exact Set.subset_centralizer_centralizer
  · intro h
    simpa [h] using wot_centralizer_closed (Set.centralizer (S : Set (H →L[ℂ] H)))

end

end VonNeumannDoubleCommutantTheorem
