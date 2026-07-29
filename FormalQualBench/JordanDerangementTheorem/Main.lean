import Mathlib.Combinatorics.Derangements.Basic
import Mathlib.GroupTheory.GroupAction.Jordan

namespace JordanDerangementTheorem

open MulAction

/-- Jordan's derangement theorem: a finite transitive permutation group on a nontrivial set contains
a derangement (equivalently, a fixed-point-free element). -/
theorem MainTheorem {α : Type*} [Finite α] [Nontrivial α]
    {G : Subgroup (Equiv.Perm α)} (hG : IsPretransitive G α) :
    ∃ g : Equiv.Perm α, g ∈ G ∧ g ∈ derangements α := by
  classical
  letI := Fintype.ofFinite α
  letI := Fintype.ofFinite G
  letI : IsPretransitive G α := hG
  letI : Unique (orbitRel.Quotient G α) :=
    Classical.choice ((pretransitive_iff_unique_quotient_of_nonempty G α).mp hG)
  letI (g : G) : Fintype (fixedBy α g) := Fintype.ofFinite _
  letI : Fintype (orbitRel.Quotient G α) := Fintype.ofFinite _
  by_contra! h
  have hfixed (g : G) : Nonempty (fixedBy α g) := by
    have hg := h (g : Equiv.Perm α) g.2
    simp only [derangements, Set.mem_setOf_eq, not_forall, not_not] at hg
    obtain ⟨x, hx⟩ := hg
    exact ⟨⟨x, by simpa using hx⟩⟩
  have hsum := sum_card_fixedBy_eq_card_orbits_mul_card_group G α
  rw [Fintype.card_unique, one_mul] at hsum
  have hle (g : G) : 1 ≤ Fintype.card (fixedBy α g) :=
    Fintype.card_pos_iff.mpr (hfixed g)
  have hlt : 1 < Fintype.card (fixedBy α (1 : G)) := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, fixedBy_one_eq_univ,
      Set.ncard_univ]
    exact Finite.one_lt_card
  rw [Fintype.card_eq_sum_ones] at hsum
  have hstrict := Finset.sum_lt_sum (s := Finset.univ) (fun g _ ↦ hle g)
    ⟨(1 : G), Finset.mem_univ _, hlt⟩
  omega

end JordanDerangementTheorem
