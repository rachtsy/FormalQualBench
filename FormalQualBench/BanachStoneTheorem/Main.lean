import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Lattice
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Maps.Proper.Basic

namespace BanachStoneTheorem

open scoped BigOperators
open Metric Set

def face {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (x : X) (ε : ℝ) : Set C(X, ℝ) :=
  {f | ‖f‖ = 1 ∧ f x = ε}

def boolSign (b : Bool) : ℝ := if b then 1 else -1

@[simp]
lemma boolSign_true : boolSign true = 1 := rfl

@[simp]
lemma boolSign_false : boolSign false = -1 := rfl

lemma abs_boolSign (b : Bool) : |boolSign b| = 1 := by
  cases b <;> simp [boolSign]

lemma boolSign_ne_zero (b : Bool) : boolSign b ≠ 0 := by
  cases b <;> simp [boolSign]

lemma boolSign_injective : Function.Injective boolSign := by
  intro b c h
  cases b <;> cases c
  · rfl
  · norm_num [boolSign] at h
  · norm_num [boolSign] at h
  · rfl

lemma exists_abs_apply_eq_norm {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [Nonempty X] (f : C(X, ℝ)) : ∃ x, |f x| = ‖f‖ := by
  obtain ⟨x, -, hx⟩ := CompactSpace.isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (map_continuous f).norm.continuousOn
  refine ⟨x, le_antisymm ?_ ?_⟩
  · simpa [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm f x
  · rw [ContinuousMap.norm_le _ (abs_nonneg (f x))]
    intro y
    simpa [Real.norm_eq_abs] using hx (Set.mem_univ y)

lemma face_convex {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (x : X) {ε : ℝ} (hε : |ε| = 1) : Convex ℝ (face x ε) := by
  intro f hf g hg a b ha hb hab
  have heval : (a • f + b • g) x = ε := by
    change a * f x + b * g x = ε
    rw [hf.2, hg.2, ← add_mul, hab, one_mul]
  refine ⟨le_antisymm ?_ ?_, heval⟩
  · calc
      ‖a • f + b • g‖ ≤ ‖a • f‖ + ‖b • g‖ := norm_add_le _ _
      _ = a * ‖f‖ + b * ‖g‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ha, abs_of_nonneg hb]
      _ = 1 := by rw [hf.1, hg.1]; linarith
  · calc
      1 = |ε| := hε.symm
      _ = |(a • f + b • g) x| := congrArg abs heval.symm
      _ ≤ ‖a • f + b • g‖ := by
        simpa [Real.norm_eq_abs] using
          ContinuousMap.norm_coe_le_norm (a • f + b • g) x

lemma face_subset_sphere {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (x : X) (ε : ℝ) : face x ε ⊆ sphere (0 : C(X, ℝ)) 1 := by
  intro f hf
  simpa [mem_sphere, dist_zero_right] using hf.1

lemma weighted_eq_one {ι : Type*} (t : Finset ι) (w : ℝ) (hw : 0 < w)
    (a : ι → ℝ) (hle : ∀ i ∈ t, a i ≤ 1)
    (hweight : ∑ _i ∈ t, w = 1) (hsum : ∑ i ∈ t, w * a i = 1) :
    ∀ i ∈ t, a i = 1 := by
  intro i hi
  apply le_antisymm (hle i hi)
  by_contra h
  have hlt : a i < 1 := lt_of_not_ge h
  have hslt : (∑ j ∈ t, w * a j) < ∑ _j ∈ t, w := by
    apply Finset.sum_lt_sum
    · intro j hj
      simpa using mul_le_mul_of_nonneg_left (hle j hj) hw.le
    · exact ⟨i, hi, by simpa using mul_lt_mul_of_pos_left hlt hw⟩
  rw [hsum, hweight] at hslt
  exact (lt_irrefl 1 hslt).elim

lemma finite_common_sign {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [Nonempty X] {A : Set C(X, ℝ)} (hconv : Convex ℝ A)
    (hsphere : A ⊆ sphere (0 : C(X, ℝ)) 1) (t : Finset C(X, ℝ))
    (ht : ∀ f ∈ t, f ∈ A) : ∃ x b, ∀ f ∈ t, f x = boolSign b := by
  classical
  by_cases htempty : t = ∅
  · exact ⟨Classical.arbitrary X, true, by simp [htempty]⟩
  have htcard : 0 < t.card :=
    Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr htempty)
  let w : ℝ := (t.card : ℝ)⁻¹
  have hw : 0 < w := inv_pos.mpr (Nat.cast_pos.mpr htcard)
  have hweight : ∑ _i ∈ t, w = (1 : ℝ) := by simp [w, htcard.ne']
  let avg : C(X, ℝ) := ∑ f ∈ t, w • f
  have havgA : avg ∈ A := by
    dsimp [avg]
    exact hconv.sum_mem (fun _ _ ↦ hw.le) hweight (fun f hf ↦ ht f hf)
  have havgnorm : ‖avg‖ = 1 := by
    simpa [mem_sphere, dist_zero_right] using hsphere havgA
  obtain ⟨x, hx⟩ := exists_abs_apply_eq_norm avg
  have habs : |avg x| = 1 := hx.trans havgnorm
  rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp habs with hpos | hneg
  · refine ⟨x, true, fun f hf ↦ ?_⟩
    exact weighted_eq_one t w hw (fun g ↦ g x) (fun g hg ↦ by
      have hgnorm : ‖g‖ = 1 := by
        simpa [mem_sphere, dist_zero_right] using hsphere (ht g hg)
      simpa [hgnorm] using ContinuousMap.apply_le_norm g x) hweight (by
        simpa [avg] using hpos) f hf
  · refine ⟨x, false, fun f hf ↦ ?_⟩
    have hf' := weighted_eq_one t w hw (fun g ↦ -g x) (fun g hg ↦ by
      have hgnorm : ‖g‖ = 1 := by
        simpa [mem_sphere, dist_zero_right] using hsphere (ht g hg)
      linarith [ContinuousMap.neg_norm_le_apply g x]) hweight (by
        simpa [avg] using congrArg Neg.neg hneg) f hf
    simp only [boolSign_false]
    linarith

def commonSignSet {X : Type*} [TopologicalSpace X]
    (f : C(X, ℝ)) : Set (X × Bool) :=
  {p | f p.1 = boolSign p.2}

lemma isClosed_commonSignSet {X : Type*} [TopologicalSpace X] (f : C(X, ℝ)) :
    IsClosed (commonSignSet f) := by
  apply isClosed_eq
  · exact f.continuous.comp continuous_fst
  · exact (show Continuous boolSign from continuous_of_discreteTopology).comp continuous_snd

lemma convex_subset_face {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [Nonempty X] {A : Set C(X, ℝ)} (hconv : Convex ℝ A)
    (hsphere : A ⊆ sphere (0 : C(X, ℝ)) 1) :
    ∃ x b, A ⊆ face x (boolSign b) := by
  classical
  have hfin : ∀ u : Finset A,
      ((Set.univ : Set (X × Bool)) ∩ ⋂ i ∈ u, commonSignSet i.1).Nonempty := by
    intro u
    let v : Finset C(X, ℝ) := u.map ⟨Subtype.val, Subtype.val_injective⟩
    obtain ⟨x, b, hxb⟩ := finite_common_sign hconv hsphere v (fun f hf ↦ by
      rcases Finset.mem_map.mp hf with ⟨a, ha, rfl⟩
      exact a.2)
    refine ⟨(x, b), Set.mem_inter (Set.mem_univ _) ?_⟩
    simp only [Set.mem_iInter]
    intro a ha
    exact hxb a.1 (Finset.mem_map.mpr ⟨a, ha, rfl⟩)
  obtain ⟨p, -, hp⟩ := CompactSpace.isCompact_univ.inter_iInter_nonempty
    (fun a : A ↦ commonSignSet (a.1 : C(X, ℝ)))
    (fun a ↦ isClosed_commonSignSet (a.1 : C(X, ℝ))) hfin
  refine ⟨p.1, p.2, fun f hf ↦ ?_⟩
  have hnorm : ‖f‖ = 1 := by
    simpa [mem_sphere, dist_zero_right] using hsphere hf
  have heval := Set.mem_iInter.mp hp ⟨f, hf⟩
  exact ⟨hnorm, heval⟩

lemma separator_mem_face {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {x y : X} (hxy : x ≠ y) (b : Bool) :
    ∃ f ∈ face x (boolSign b), f y = -boolSign b := by
  obtain ⟨h, hx, hy, hrange⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_singleton : IsClosed ({x} : Set X))
    (isClosed_singleton : IsClosed ({y} : Set X)) (Set.disjoint_singleton.mpr hxy)
  let f : C(X, ℝ) := boolSign b • (1 - (2 : ℝ) • h)
  have hfx : f x = boolSign b := by
    dsimp [f]
    change boolSign b * (1 - (2 : ℝ) • h x) = boolSign b
    rw [hx (Set.mem_singleton x)]
    norm_num
  have hfy : f y = -boolSign b := by
    dsimp [f]
    change boolSign b * (1 - (2 : ℝ) • h y) = -boolSign b
    rw [hy (Set.mem_singleton y)]
    norm_num
  have hnorm_le : ‖f‖ ≤ 1 := by
    rw [ContinuousMap.norm_le _ zero_le_one]
    intro z
    dsimp [f]
    change |boolSign b * (1 - (2 : ℝ) • h z)| ≤ 1
    rw [abs_mul, abs_boolSign, one_mul, abs_le]
    constructor <;> simp only [smul_eq_mul] <;>
      nlinarith [(hrange z).1, (hrange z).2]
  have hnorm_ge : 1 ≤ ‖f‖ := by
    calc
      1 = |boolSign b| := (abs_boolSign b).symm
      _ = |f x| := congrArg abs hfx.symm
      _ ≤ ‖f‖ := by
        simpa [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm f x
  exact ⟨f, ⟨le_antisymm hnorm_le hnorm_ge, hfx⟩, hfy⟩

lemma face_subset_face {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [Nonempty X] {x y : X} {b c : Bool}
    (h : face x (boolSign b) ⊆ face y (boolSign c)) : x = y ∧ b = c := by
  have hconst : boolSign b • (1 : C(X, ℝ)) ∈ face x (boolSign b) := by
    refine ⟨?_, by simp⟩
    rw [norm_smul, Real.norm_eq_abs, abs_boolSign, norm_one, one_mul]
  have hsignequal : boolSign b = boolSign c := by
    have := (h hconst).2
    simpa using this
  have hbc : b = c := boolSign_injective hsignequal
  refine ⟨?_, hbc⟩
  by_contra hxy
  obtain ⟨f, hfx, hfy⟩ := separator_mem_face hxy b
  have hfy' := (h hfx).2
  rw [hbc] at hfy
  have : boolSign c = 0 := by linarith
  exact boolSign_ne_zero c this

lemma face_maximal {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [Nonempty X] (x : X) (b : Bool) {B : Set C(X, ℝ)}
    (hconv : Convex ℝ B) (hsphere : B ⊆ sphere (0 : C(X, ℝ)) 1)
    (hsub : face x (boolSign b) ⊆ B) : B ⊆ face x (boolSign b) := by
  obtain ⟨y, c, hB⟩ := convex_subset_face hconv hsphere
  obtain ⟨hxy, hbc⟩ := face_subset_face (hsub.trans hB)
  simpa [hxy, hbc] using hB

lemma exists_image_face_eq_face
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
    (e : C(X, ℝ) ≃ₗᵢ[ℝ] C(Y, ℝ)) (x : X) (b : Bool) :
    ∃ y c, e '' face x (boolSign b) = face y (boolSign c) := by
  have hconv : Convex ℝ (e '' face x (boolSign b)) :=
    (face_convex x (abs_boolSign b)).linear_image e.toLinearEquiv.toLinearMap
  have hsphere : e '' face x (boolSign b) ⊆ sphere (0 : C(Y, ℝ)) 1 := by
    rintro _ ⟨f, hf, rfl⟩
    simp [hf.1]
  obtain ⟨y, c, hsub⟩ := convex_subset_face hconv hsphere
  refine ⟨y, c, hsub.antisymm ?_⟩
  intro g hg
  have hsource : face x (boolSign b) ⊆ e.symm '' face y (boolSign c) := by
    intro f hf
    exact ⟨e f, hsub ⟨f, hf, rfl⟩, e.symm_apply_apply f⟩
  have hpreconv : Convex ℝ (e.symm '' face y (boolSign c)) :=
    (face_convex y (abs_boolSign c)).linear_image e.symm.toLinearEquiv.toLinearMap
  have hpresphere : e.symm '' face y (boolSign c) ⊆ sphere (0 : C(X, ℝ)) 1 := by
    rintro _ ⟨f, hf, rfl⟩
    simp [hf.1]
  have hpre := face_maximal x b hpreconv hpresphere hsource
  exact ⟨e.symm g, hpre ⟨g, hg, rfl⟩, e.apply_symm_apply g⟩

noncomputable def pointMap
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
    (e : C(X, ℝ) ≃ₗᵢ[ℝ] C(Y, ℝ)) (y : Y) : X :=
  Classical.choose (exists_image_face_eq_face e.symm y true)

noncomputable def pointSign
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
    (e : C(X, ℝ) ≃ₗᵢ[ℝ] C(Y, ℝ)) (y : Y) : Bool :=
  Classical.choose (Classical.choose_spec (exists_image_face_eq_face e.symm y true))

lemma pointMap_spec
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
    (e : C(X, ℝ) ≃ₗᵢ[ℝ] C(Y, ℝ)) (y : Y) :
    e.symm '' face y 1 = face (pointMap e y) (boolSign (pointSign e y)) :=
  Classical.choose_spec (Classical.choose_spec (exists_image_face_eq_face e.symm y true))

lemma map_face_apply
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
    (e : C(X, ℝ) ≃ₗᵢ[ℝ] C(Y, ℝ)) (y : Y) {f : C(X, ℝ)}
    (hf : f ∈ face (pointMap e y) (boolSign (pointSign e y))) : e f y = 1 := by
  have hf' : f ∈ e.symm '' face y 1 := by
    rw [pointMap_spec e y]
    exact hf
  obtain ⟨g, hg, hgf⟩ := hf'
  have heq : e f = g := by
    rw [← hgf, e.apply_symm_apply]
  rw [heq]
  exact hg.2

lemma map_one_apply
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
    (e : C(X, ℝ) ≃ₗᵢ[ℝ] C(Y, ℝ)) (y : Y) :
    e (1 : C(X, ℝ)) y = boolSign (pointSign e y) := by
  let b := pointSign e y
  have hface : boolSign b • (1 : C(X, ℝ)) ∈ face (pointMap e y) (boolSign b) := by
    refine ⟨?_, by simp⟩
    rw [norm_smul, Real.norm_eq_abs, abs_boolSign, norm_one, one_mul]
  have h := map_face_apply e y hface
  cases hb : b
  · simp [b, hb] at h ⊢
    linarith
  · simpa [b, hb] using h

lemma abs_perturb_le (b : Bool) {δ a : ℝ} (hδ : 0 ≤ δ)
    (hδa : δ * |a| ≤ 1) :
    |boolSign b * (1 - δ * |a|) + δ * a| ≤ 1 ∧
      |boolSign b * (1 - δ * |a|) - δ * a| ≤ 1 := by
  cases b <;> simp only [boolSign_false, boolSign_true, neg_mul, one_mul]
  all_goals rw [abs_le, abs_le]
  all_goals constructor
  all_goals constructor <;> nlinarith [le_abs_self a, neg_le_abs a]

lemma map_apply_eq_zero_of_apply_eq_zero
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
    (e : C(X, ℝ) ≃ₗᵢ[ℝ] C(Y, ℝ)) (f : C(X, ℝ)) (y : Y)
    (hf : f (pointMap e y) = 0) : e f y = 0 := by
  let δ : ℝ := (‖f‖ + 1)⁻¹
  have hδ : 0 < δ := inv_pos.mpr (by positivity)
  have hδnorm : δ * ‖f‖ ≤ 1 := by
    rw [show δ * ‖f‖ = ‖f‖ / (‖f‖ + 1) by
      simp [δ, div_eq_mul_inv, mul_comm]]
    exact (div_le_one (by positivity)).mpr (by linarith [norm_nonneg f])
  let base : C(X, ℝ) :=
    boolSign (pointSign e y) • (1 - δ • |f|)
  let fplus : C(X, ℝ) := base + δ • f
  let fminus : C(X, ℝ) := base - δ • f
  have hδapply (x : X) : δ * |f x| ≤ 1 := by
    have hx : |f x| ≤ ‖f‖ := by
      simpa [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm f x
    exact (mul_le_mul_of_nonneg_left hx hδ.le).trans hδnorm
  have hplus_le : ‖fplus‖ ≤ 1 := by
    rw [ContinuousMap.norm_le _ zero_le_one]
    intro x
    change |boolSign (pointSign e y) * (1 - δ * |f x|) + δ * f x| ≤ 1
    exact (abs_perturb_le (pointSign e y) hδ.le (hδapply x)).1
  have hminus_le : ‖fminus‖ ≤ 1 := by
    rw [ContinuousMap.norm_le _ zero_le_one]
    intro x
    change |boolSign (pointSign e y) * (1 - δ * |f x|) - δ * f x| ≤ 1
    exact (abs_perturb_le (pointSign e y) hδ.le (hδapply x)).2
  have hplus_apply : fplus (pointMap e y) = boolSign (pointSign e y) := by
    simp [fplus, base, hf]
  have hminus_apply : fminus (pointMap e y) = boolSign (pointSign e y) := by
    simp [fminus, base, hf]
  have hplus_ge : 1 ≤ ‖fplus‖ := by
    have h := ContinuousMap.norm_coe_le_norm fplus (pointMap e y)
    simpa [Real.norm_eq_abs, hplus_apply, abs_boolSign] using h
  have hminus_ge : 1 ≤ ‖fminus‖ := by
    have h := ContinuousMap.norm_coe_le_norm fminus (pointMap e y)
    simpa [Real.norm_eq_abs, hminus_apply, abs_boolSign] using h
  have hplus_face : fplus ∈ face (pointMap e y) (boolSign (pointSign e y)) :=
    ⟨le_antisymm hplus_le hplus_ge, hplus_apply⟩
  have hminus_face : fminus ∈ face (pointMap e y) (boolSign (pointSign e y)) :=
    ⟨le_antisymm hminus_le hminus_ge, hminus_apply⟩
  have heplus := map_face_apply e y hplus_face
  have heminus := map_face_apply e y hminus_face
  simp only [fplus, fminus, map_add, map_sub, map_smul, ContinuousMap.add_apply,
    ContinuousMap.sub_apply] at heplus heminus
  change e base y + δ * e f y = 1 at heplus
  change e base y - δ * e f y = 1 at heminus
  nlinarith

lemma map_apply_eq
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
    (e : C(X, ℝ) ≃ₗᵢ[ℝ] C(Y, ℝ)) (f : C(X, ℝ)) (y : Y) :
    e f y = boolSign (pointSign e y) * f (pointMap e y) := by
  let g : C(X, ℝ) := f - f (pointMap e y) • (1 : C(X, ℝ))
  have hg : g (pointMap e y) = 0 := by simp [g]
  have hzero := map_apply_eq_zero_of_apply_eq_zero e g y hg
  simp only [g, map_sub, map_smul, ContinuousMap.sub_apply] at hzero
  change e f y - f (pointMap e y) * e (1 : C(X, ℝ)) y = 0 at hzero
  rw [map_one_apply] at hzero
  linarith

lemma continuous_pointMap
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
    (e : C(X, ℝ) ≃ₗᵢ[ℝ] C(Y, ℝ)) : Continuous (pointMap e) := by
  rw [continuous_def]
  intro U hU
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨f, hcompl, hx, -⟩ := exists_continuous_zero_one_of_isClosed
    hU.isClosed_compl (isClosed_singleton : IsClosed ({pointMap e y} : Set X))
    (Set.disjoint_singleton_right.mpr (by simpa using hy))
  let V : Set Y := {z | (1 : ℝ) / 2 < |e f z|}
  have hVopen : IsOpen V :=
    isOpen_lt continuous_const (map_continuous (e f)).abs
  have hVmem : y ∈ V := by
    change (1 : ℝ) / 2 < |e f y|
    have hmap := map_apply_eq e f y
    have hfx : f (pointMap e y) = 1 := hx (Set.mem_singleton _)
    rw [hmap, hfx, mul_one, abs_boolSign]
    norm_num
  refine Filter.mem_of_superset (hVopen.mem_nhds hVmem) ?_
  intro z hz
  change pointMap e z ∈ U
  by_contra hnot
  have hfzero : f (pointMap e z) = 0 := hcompl (by simpa using hnot)
  have hmap := map_apply_eq e f z
  rw [hfzero, mul_zero] at hmap
  have : (1 : ℝ) / 2 < 0 := by simpa [V, hmap] using hz
  norm_num at this

lemma pointMap_symm_apply
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
    (e : C(X, ℝ) ≃ₗᵢ[ℝ] C(Y, ℝ)) (y : Y) :
    pointMap e.symm (pointMap e y) = y := by
  let x := pointMap e y
  let y' := pointMap e.symm x
  let s := boolSign (pointSign e y)
  let t := boolSign (pointSign e.symm x)
  have hprod : s * t = 1 := by
    have h₁ := map_apply_eq e (e.symm (1 : C(Y, ℝ))) y
    rw [e.apply_symm_apply] at h₁
    have h₂ := map_apply_eq e.symm (1 : C(Y, ℝ)) x
    have h₂' : e.symm (1 : C(Y, ℝ)) x = t := by simpa [t] using h₂
    rw [h₂'] at h₁
    simpa [s] using h₁.symm
  have hfun : ∀ g : C(Y, ℝ), g y = g y' := by
    intro g
    have h₁ := map_apply_eq e (e.symm g) y
    rw [e.apply_symm_apply] at h₁
    have h₂ := map_apply_eq e.symm g x
    change e.symm g x = t * g y' at h₂
    rw [h₂] at h₁
    calc
      g y = s * (t * g y') := by simpa [s] using h₁
      _ = (s * t) * g y' := by ring
      _ = g y' := by rw [hprod, one_mul]
  by_contra hne
  obtain ⟨g, hy, hy', -⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_singleton : IsClosed ({y} : Set Y))
    (isClosed_singleton : IsClosed ({y'} : Set Y))
    (Set.disjoint_singleton.mpr (by
      intro h
      exact hne (by simpa [y'] using h.symm)))
  have := hfun g
  rw [hy (Set.mem_singleton y), hy' (Set.mem_singleton y')] at this
  norm_num at this

lemma pointMap_apply_symm
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
    (e : C(X, ℝ) ≃ₗᵢ[ℝ] C(Y, ℝ)) (x : X) :
    pointMap e (pointMap e.symm x) = x := by
  simpa using pointMap_symm_apply e.symm x

noncomputable def pointEquiv
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
    (e : C(X, ℝ) ≃ₗᵢ[ℝ] C(Y, ℝ)) : Y ≃ X where
  toFun := pointMap e
  invFun := pointMap e.symm
  left_inv := pointMap_symm_apply e
  right_inv := pointMap_apply_symm e

/-- Banach-Stone theorem for real-valued continuous functions on compact Hausdorff spaces. -/
theorem MainTheorem (X Y : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (e : C(X, ℝ) ≃ₗᵢ[ℝ] C(Y, ℝ)) :
    Nonempty (X ≃ₜ Y) := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · rcases isEmpty_or_nonempty Y with hY | hY
    · letI : IsEmpty X := hX
      letI : IsEmpty Y := hY
      exact ⟨Homeomorph.empty⟩
    · letI : IsEmpty X := hX
      letI : Nonempty Y := hY
      haveI : Subsingleton C(Y, ℝ) := e.surjective.subsingleton
      exact (one_ne_zero (α := C(Y, ℝ)) (Subsingleton.elim 1 0)).elim
  · rcases isEmpty_or_nonempty Y with hY | hY
    · letI : Nonempty X := hX
      letI : IsEmpty Y := hY
      haveI : Subsingleton C(X, ℝ) := e.injective.subsingleton
      exact (one_ne_zero (α := C(X, ℝ)) (Subsingleton.elim 1 0)).elim
    · letI : Nonempty X := hX
      letI : Nonempty Y := hY
      exact ⟨(Continuous.homeoOfEquivCompactToT2
        (f := pointEquiv e) (continuous_pointMap e)).symm⟩

end BanachStoneTheorem
