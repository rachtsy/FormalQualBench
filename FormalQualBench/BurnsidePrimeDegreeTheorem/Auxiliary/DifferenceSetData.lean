import Mathlib
import FormalQualBench.BurnsidePrimeDegreeTheorem.Auxiliary.TauOrbitEquiv

namespace BurnsidePrimeDegreeTheorem

open MulAction

lemma difference_set_data
    {α : Type*} [Fintype α] [NeZero (Fintype.card α)]
    {G : Subgroup (Equiv.Perm α)} [IsPretransitive G α]
    (hp : (Fintype.card α).Prime)
    (τ : G) (hord : orderOf τ = Fintype.card α) :
    ∃ U : Finset (ZMod (Fintype.card α)),
      U.Nonempty ∧ 0 ∉ U ∧ U ⊆ Finset.univ.erase 0 ∧
      ∀ g : G, ∀ i j : ZMod (Fintype.card α), i - j ∈ U →
        ((tauOrbitEquiv τ hp hord).trans (g : Equiv.Perm α) |>.trans
          (tauOrbitEquiv τ hp hord).symm) i -
        ((tauOrbitEquiv τ hp hord).trans (g : Equiv.Perm α) |>.trans
          (tauOrbitEquiv τ hp hord).symm) j ∈ U := by
  classical
  haveI : Fact (Fintype.card α).Prime := ⟨hp⟩
  let e := tauOrbitEquiv τ hp hord
  let U : Finset (ZMod (Fintype.card α)) := Finset.univ.filter fun d ↦
    d ≠ 0 ∧ ∃ h : G, h • e 1 = e d ∧ h • e 0 = e 0
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · refine ⟨1, ?_⟩
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨one_ne_zero, 1, ?_, ?_⟩ <;> simp
  · simp [U]
  · intro d hd
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hd).2.1, Finset.mem_univ d⟩
  · intro g i j hij
    let π : Equiv.Perm (ZMod (Fintype.card α)) :=
      (e.trans (g : Equiv.Perm α)).trans e.symm
    have hπ (x : ZMod (Fintype.card α)) : e (π x) = g • e x := by
      change e (e.symm ((g : Equiv.Perm α) (e x))) = (g : Equiv.Perm α) (e x)
      rw [e.apply_symm_apply]
    have hπ' (x : ZMod (Fintype.card α)) : (g : Equiv.Perm α) (e x) = e (π x) := by
      simpa using (hπ x).symm
    have hd := (Finset.mem_filter.mp hij).2
    obtain ⟨hd0, h, hh1, hh0⟩ := hd
    have hijne : i ≠ j := sub_ne_zero.mp hd0
    have hpijne : π i ≠ π j := π.injective.ne hijne
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, sub_ne_zero.mpr hpijne, ?_⟩
    let k : G := τ ^ (-π j).val * g * τ ^ j.val * h
    refine ⟨k, ?_, ?_⟩
    · change ((τ : Equiv.Perm α) ^ (-π j).val)
        ((g : Equiv.Perm α) (((τ : Equiv.Perm α) ^ j.val) (h • e 1))) =
          e (π i - π j)
      rw [hh1]
      rw [← tauOrbitEquiv_add τ hp hord]
      change ((τ : Equiv.Perm α) ^ (-π j).val)
        ((g : Equiv.Perm α) (e (j + (i - j)))) = e (π i - π j)
      have hji : j + (i - j) = i := by ring
      rw [hji]
      rw [hπ' i]
      change ((τ : Equiv.Perm α) ^ (-π j).val) (e (π i)) = e (π i - π j)
      rw [← tauOrbitEquiv_add τ hp hord]
      congr 1
      ring
    · change ((τ : Equiv.Perm α) ^ (-π j).val)
        ((g : Equiv.Perm α) (((τ : Equiv.Perm α) ^ j.val) (h • e 0))) = e 0
      rw [hh0]
      rw [← tauOrbitEquiv_add τ hp hord]
      change ((τ : Equiv.Perm α) ^ (-π j).val)
        ((g : Equiv.Perm α) (e (j + 0))) = e 0
      simp only [add_zero]
      rw [hπ' j]
      rw [← tauOrbitEquiv_add τ hp hord]
      congr 1
      ring

end BurnsidePrimeDegreeTheorem
