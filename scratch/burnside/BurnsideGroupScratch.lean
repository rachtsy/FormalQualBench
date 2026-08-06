import Mathlib
import FormalQualBench.BurnsidePrimeDegreeTheorem.Auxiliary.PrimeOrderCyclicAction

namespace BurnsidePrimeDegreeTheorem

open MulAction

noncomputable def tauOrbitEquiv
    {α : Type*} [Fintype α] {G : Subgroup (Equiv.Perm α)}
    (τ : G) (hp : (Fintype.card α).Prime)
    (hord : orderOf τ = Fintype.card α) : ZMod (Fintype.card α) ≃ α := by
  classical
  haveI : Fact (Fintype.card α).Prime := ⟨hp⟩
  let σ : Equiv.Perm α := τ
  have hcycle : σ.IsCycle := prime_order_element_isCycle τ hp hord
  have hsupp : σ.support = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← hcycle.orderOf]
    exact (Subgroup.orderOf_mk (τ : Equiv.Perm α) τ.2).symm.trans hord
  let a : α := Classical.choose hcycle
  have ha : a ∈ σ.support := by
    rw [hsupp]
    exact Finset.mem_univ a
  let f : ZMod (Fintype.card α) → α := fun i ↦ (σ ^ i.val) a
  have hinj : Function.Injective f := by
    intro i j hij
    apply ZMod.val_injective (Fintype.card α)
    have hpows : σ ^ i.val = σ ^ j.val :=
      hcycle.pow_eq_pow_iff.mpr ⟨a, Classical.choose_spec hcycle |>.1, hij⟩
    have hmod : i.val ≡ j.val [MOD orderOf σ] := pow_eq_pow_iff_modEq.mp hpows
    have horder : orderOf σ = Fintype.card α := by
      rw [hcycle.orderOf, hsupp, Finset.card_univ]
    rw [horder] at hmod
    have hi : i.val % Fintype.card α = i.val := Nat.mod_eq_of_lt i.val_lt
    have hj : j.val % Fintype.card α = j.val := Nat.mod_eq_of_lt j.val_lt
    rw [Nat.ModEq] at hmod
    simpa [hi, hj] using hmod
  refine Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, ?_⟩)
  rw [ZMod.card]

lemma tauOrbitEquiv_apply
    {α : Type*} [Fintype α] {G : Subgroup (Equiv.Perm α)}
    (τ : G) (hp : (Fintype.card α).Prime)
    (hord : orderOf τ = Fintype.card α) (i : ZMod (Fintype.card α)) :
    tauOrbitEquiv τ hp hord i =
      ((τ : Equiv.Perm α) ^ i.val) (Classical.choose (prime_order_element_isCycle τ hp hord)) := by
  rfl

lemma tauOrbitEquiv_add
    {α : Type*} [Fintype α] {G : Subgroup (Equiv.Perm α)}
    (τ : G) (hp : (Fintype.card α).Prime)
    (hord : orderOf τ = Fintype.card α)
    (i j : ZMod (Fintype.card α)) :
    tauOrbitEquiv τ hp hord (i + j) =
      ((τ : Equiv.Perm α) ^ i.val) (tauOrbitEquiv τ hp hord j) := by
  letI : NeZero (Fintype.card α) := ⟨hp.ne_zero⟩
  rw [tauOrbitEquiv_apply, tauOrbitEquiv_apply]
  rw [← Equiv.Perm.mul_apply, ← pow_add]
  apply congrArg (fun g : Equiv.Perm α ↦
    g (Classical.choose (prime_order_element_isCycle τ hp hord)))
  rw [pow_eq_pow_iff_modEq]
  have horder : orderOf (τ : Equiv.Perm α) = Fintype.card α :=
    (Subgroup.orderOf_mk (τ : Equiv.Perm α) τ.2).symm.trans hord
  rw [horder]
  exact (ZMod.natCast_eq_natCast_iff' (i + j).val (i.val + j.val)
    (Fintype.card α)).mp (by
      rw [ZMod.natCast_zmod_val, Nat.cast_add, ZMod.natCast_zmod_val,
        ZMod.natCast_zmod_val])

end BurnsidePrimeDegreeTheorem
