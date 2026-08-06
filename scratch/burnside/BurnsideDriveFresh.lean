import Mathlib

namespace BurnsidePrimeDegreeTheorem

open MulAction Equiv.Perm Subgroup

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ## Helper lemmas -/

/-- p² does not divide p! for prime p. -/
lemma prime_sq_not_dvd_factorial {p : ℕ} (hp : p.Prime) : ¬ (p ^ 2 ∣ p.factorial) := by
  induction' p with p hp <;> simp_all +decide [ Nat.factorial_succ, sq, mul_assoc, hp.ne_one ]
  rw [ Nat.mul_dvd_mul_iff_left hp.pos ]
  rw [ Nat.Prime.dvd_factorial ] <;> aesop

/-- The p-adic valuation of |G| is 1 when G is a transitive subgroup of S_p (p prime). -/
lemma factorization_card_eq_one
    {G : Subgroup (Equiv.Perm α)}
    (htrans : IsPretransitive G α) (hp : (Fintype.card α).Prime) :
    (Nat.card G).factorization (Fintype.card α) = 1 := by
  have h_divides_factorial : Fintype.card α ∣ Nat.card G ∧ Nat.card G ∣ Nat.factorial (Fintype.card α) := by
    constructor
    · obtain ⟨a, ha⟩ : ∃ a : α, True := by
        exact ⟨ Classical.choose ( Finset.card_pos.mp hp.pos ), trivial ⟩
      have h_orbit : Nat.card (MulAction.orbit G a) = Fintype.card α := by
        simp +decide [ Nat.card_eq_fintype_card, SetLike.ext_iff ]
        rw [ show orbit ( G ) a = Set.univ from Set.eq_univ_iff_forall.mpr fun b => by rcases htrans.exists_smul_eq a b with ⟨ g, hg ⟩ ; aesop ] ; simp +decide [ Set.ncard_univ ]
      have h_orbit_divides : Nat.card (MulAction.orbit G a) ∣ Nat.card G := by
        convert Subgroup.card_quotient_dvd_card ( MulAction.stabilizer G a ) using 1
        exact Nat.card_congr ( MulAction.orbitEquivQuotientStabilizer _ _ )
      aesop
    · convert Subgroup.card_subgroup_dvd_card G
      simp +decide [ Fintype.card_perm ]
  obtain ⟨ k, hk ⟩ := h_divides_factorial.1
  rw [ hk, Nat.factorization_mul ] <;> simp +decide [ hp.ne_zero ]
  · simp +decide [ hp.factorization ]
    refine' Nat.factorization_eq_zero_of_not_dvd _
    intro h
    have h_contradiction : Fintype.card α ^ 2 ∣ Nat.factorial (Fintype.card α) := by
      exact dvd_trans ( by rw [ sq ] ; exact mul_dvd_mul_left _ h ) ( hk.symm ▸ h_divides_factorial.2 )
    exact absurd h_contradiction ( prime_sq_not_dvd_factorial hp )
  · nlinarith [ hp.two_le, show Nat.card G > 0 from Nat.card_pos ]

/-- A Sylow p-subgroup of a transitive group on p elements has order p. -/
lemma sylow_card_eq_prime
    {G : Subgroup (Equiv.Perm α)}
    (htrans : IsPretransitive G α) (hp : (Fintype.card α).Prime) :
    ∀ P : Sylow (Fintype.card α) G, Nat.card P = Fintype.card α := by
  intro P
  have hP_order : Nat.card P = (Nat.card G).factorization (Fintype.card α) * Fintype.card α := by
    have := Fact.mk hp
    have := Sylow.card_eq_multiplicity P
    have := factorization_card_eq_one htrans hp; aesop
  have := factorization_card_eq_one htrans hp; aesop

/-- A group of prime order p = |α| acting faithfully on α acts transitively. -/
lemma pretransitive_of_prime_card
    {G : Type*} [Group G] [MulAction G α] [FaithfulSMul G α]
    (hp : (Fintype.card α).Prime)
    (hcard : Nat.card G = Fintype.card α) :
    IsPretransitive G α := by
  have h_orbit_size : ∀ x : α, (Nat.card (MulAction.orbit G x)) ∣ Fintype.card α := by
    intro x
    have h_orbit_size : (Nat.card (MulAction.orbit G x)) ∣ (Nat.card G) := by
      convert Subgroup.card_quotient_dvd_card ( MulAction.stabilizer G x )
      exact Nat.card_congr ( MulAction.orbitEquivQuotientStabilizer G x )
    aesop
  obtain ⟨x, hx⟩ : ∃ x : α, 1 < Nat.card (MulAction.orbit G x) := by
    by_contra h_contra
    push_neg at h_contra
    have h_single_orbit : ∀ x : α, MulAction.orbit G x = {x} := by
      intro x
      have h_orbit_singleton : Nat.card (MulAction.orbit G x) = 1 := by
        exact le_antisymm ( h_contra x ) ( Nat.pos_of_dvd_of_pos ( h_orbit_size x ) hp.pos )
      have h_orbit_eq_singleton : MulAction.orbit G x = {x} := by
        simp_all +decide [ Set.eq_singleton_iff_unique_mem ]
        exact fun y hy => by obtain ⟨ g, rfl ⟩ := hy; exact h_contra x g
      exact h_orbit_eq_singleton
    have h_trivial : ∀ g : G, ∀ x : α, g • x = x := by
      exact fun g x => by simpa using Set.ext_iff.mp ( h_single_orbit x ) ( g • x ) |>.1 ( MulAction.mem_orbit _ _ )
    have h_card : Nat.card G = 1 := by
      rw [ Nat.card_eq_one_iff_unique ]
      exact ⟨ ⟨ fun g₁ g₂ => by simpa [ h_trivial ] using ( ‹FaithfulSMul G α›.eq_of_smul_eq_smul ( fun x => by simp +decide [ h_trivial ] ) ) ⟩, ⟨ 1 ⟩ ⟩
    have h_contra : Fintype.card α = 1 := by
      linarith
    exact absurd h_contra (Nat.Prime.ne_one hp)
  simp_all +decide [ Nat.dvd_prime hp ]
  have h_orbit_eq_univ : MulAction.orbit G x = Set.univ := by
    exact Set.eq_of_subset_of_ncard_le ( Set.subset_univ _ ) ( by simp +decide [ hcard, hx, h_orbit_size x |> Or.resolve_left <| by aesop ] )
  exact?

/-- A transitive group of prime order p = |α| has trivial point stabilizers. -/
lemma stabilizer_eq_bot_of_prime_card
    {G : Type*} [Group G] [MulAction G α]
    (hp : (Fintype.card α).Prime)
    (hcard : Nat.card G = Fintype.card α)
    (htrans : IsPretransitive G α) :
    ∀ a : α, MulAction.stabilizer G a = ⊥ := by
  have h_orbit_stabilizer : ∀ a : α, Nat.card (MulAction.stabilizer G a) * Nat.card (MulAction.orbit G a) = Nat.card G := by
    intro a
    have h_orbit_stabilizer : Nat.card (MulAction.orbit G a) * Nat.card (MulAction.stabilizer G a) = Nat.card G := by
      rw [ ← Nat.card_prod, ← Nat.card_congr ( MulAction.orbitProdStabilizerEquivGroup G a ) ]
    linarith [h_orbit_stabilizer]
  have h_orbit : ∀ a : α, Nat.card (MulAction.orbit G a) = Fintype.card α := by
    exact fun a => by rw [ show ( MulAction.orbit G a : Set α ) = Set.univ from Set.eq_univ_iff_forall.mpr fun b => by obtain ⟨ g, hg ⟩ := htrans.exists_smul_eq a b; exact ⟨ g, hg ⟩ ] ; simp +decide [ Nat.card_eq_fintype_card ]
  intro a
  have h_stabilizer_card : Nat.card (MulAction.stabilizer G a) = 1 := by
    nlinarith [ h_orbit_stabilizer a, h_orbit a, hp.two_le ]
  exact?

/-
PROBLEM
An element of order p in S_p (p prime) has no fixed points. Its support is all of α.

PROVIDED SOLUTION
An element g of order p in S_p (where |α| = p, p prime) must be a single p-cycle. Since g has order p (prime), each cycle in its decomposition has length dividing p, so length 1 or p. Since the order is the lcm of cycle lengths, and the order is p ≥ 2, at least one cycle has length p. Since the total number of elements is p, there's exactly one p-cycle and no fixed points. Hence g.support = Finset.univ.

Use Equiv.Perm.IsCycle.orderOf (if g is a cycle, orderOf g = support.card), and the fact that if g has order p prime in S_p then g must be a single p-cycle. Alternatively, use g.support.card = p - card(fixedPoints) and show fixedPoints is empty. Since g has order p in S_p with p prime, g.cycleType has only entries equal to p or 1. Since lcm of cycleType = p, there's an entry p. Since sum of cycleType = p, the only possibility is cycleType = {p}. Hence support = univ.
-/
lemma support_eq_univ_of_orderOf_eq_prime
    (hp : (Fintype.card α).Prime)
    (g : Equiv.Perm α) (hord : orderOf g = Fintype.card α) :
    g.support = Finset.univ := by
  -- Since $g$ is an element of order $p$ in $S_p$, its cycle type must be a single $p$-cycle.
  have h_cycle_type : g.cycleType = {Fintype.card α} := by
    have h_cycle_type : g.cycleType.lcm = Fintype.card α := by
      rw [ ← hord, Equiv.Perm.lcm_cycleType ]
    have h_cycle_length : ∀ c ∈ g.cycleType, c = Fintype.card α := by
      intro c hc
      have h_divides : c ∣ Fintype.card α := by
        exact h_cycle_type ▸ Multiset.dvd_lcm hc
      have h_divides' : c ∣ Fintype.card α := by
        exact h_divides
      have h_divides'' : c = 1 ∨ c = Fintype.card α := by
        rwa [ Nat.dvd_prime hp ] at h_divides'
      cases' h_divides'' with h h <;> simp_all +decide [ Nat.dvd_prime hp ];
      rw [ Equiv.Perm.mem_cycleType_iff ] at hc;
      obtain ⟨ c, τ, rfl, hcd, hc, hc' ⟩ := hc; have := hc.orderOf; simp_all +decide [ Nat.Prime.ne_one hp ] ;
    have h_cycle_type_form : ∃ k : ℕ, g.cycleType = Multiset.replicate k (Fintype.card α) := by
      exact ⟨ Multiset.card g.cycleType, Multiset.eq_replicate_of_mem h_cycle_length ⟩
    obtain ⟨k, hk⟩ := h_cycle_type_form
    have hk_one : k = 1 := by
      have h_cycle_type_sum : (g.cycleType.sum : ℕ) ≤ Fintype.card α := by
        exact?;
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.Prime.ne_zero ] ; nlinarith [ hp.two_le ] ;
    rw [hk, hk_one]
    simp +decide [hp];
  have := Equiv.Perm.sum_cycleType g; simp_all +decide ;
  exact Finset.eq_of_subset_of_card_le ( Finset.subset_univ _ ) ( by simp +decide [ this ] )

/-
PROBLEM
In a transitive group on p elements (p prime), an element of order p has no fixed
points (i.e., the number of fixed points is 0).

PROVIDED SOLUTION
The element g has order p = Fintype.card α in Perm α. By support_eq_univ_of_orderOf_eq_prime, g.support = Finset.univ. This means g moves every point, so no point is fixed. Hence fixedBy α g = ∅ and its cardinality is 0.

Note: fixedBy α g = {x : α | g • x = x} = {x : α | (g : Perm α) x = x}. Since g.support = univ, every x satisfies g x ≠ x, so fixedBy is empty.
-/
lemma card_fixedBy_eq_zero_of_orderOf_eq_prime
    {G : Subgroup (Equiv.Perm α)}
    (hp : (Fintype.card α).Prime)
    (g : G) (hord : orderOf (g : Equiv.Perm α) = Fintype.card α) :
    Fintype.card (MulAction.fixedBy α (g : Equiv.Perm α)) = 0 := by
  have := support_eq_univ_of_orderOf_eq_prime hp ( g : Equiv.Perm α ) hord; simp_all +decide [ Equiv.Perm.mem_support, Fintype.card_subtype ] ;
  intro x hx; replace this := Finset.ext_iff.mp this x; aesop;

/-
PROBLEM
Distinct Sylow p-subgroups of prime order intersect trivially.

PROVIDED SOLUTION
P and Q are distinct Sylow p-subgroups with |P| = |Q| = p (prime) (by sylow_card_eq_prime). The intersection P ∩ Q is a subgroup of P, so |P ∩ Q| divides |P| = p. Since p is prime, |P ∩ Q| = 1 or p. If |P ∩ Q| = p, then P ∩ Q = P (since |P| = p), so P ≤ Q. But |P| = |Q| = p, so P = Q. Contradiction with P ≠ Q. So |P ∩ Q| = 1, meaning P ∩ Q = ⊥.
-/
lemma sylow_inf_eq_bot_of_ne
    {G : Subgroup (Equiv.Perm α)}
    (htrans : IsPretransitive G α) (hp : (Fintype.card α).Prime)
    (P Q : Sylow (Fintype.card α) G) (hPQ : P ≠ Q) :
    (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥ := by
  -- Since $P$ and $Q$ are distinct Sylow $p$-subgroups, their intersection $P \cap Q$ is a proper subgroup of $P$.
  have h_inter_proper : (P : Subgroup G) ⊓ (Q : Subgroup G) < P := by
    simp_all +decide [ lt_iff_le_and_ne ];
    contrapose! hPQ;
    have h_card : Nat.card P = Nat.card Q := by
      have hPQ_card : Nat.card P = Fintype.card α ∧ Nat.card Q = Fintype.card α := by
        exact ⟨ sylow_card_eq_prime htrans hp P, sylow_card_eq_prime htrans hp Q ⟩;
      rw [ hPQ_card.1, hPQ_card.2 ];
    have h_eq : (P : Set G) = (Q : Set G) := by
      exact Set.eq_of_subset_of_ncard_le hPQ ( by simpa [ Set.ncard_eq_toFinset_card' ] using h_card.ge );
    exact SetLike.ext' h_eq;
  -- Since $P$ and $Q$ are distinct Sylow $p$-subgroups, their intersection $P \cap Q$ is a proper subgroup of $P$, and hence has order less than $p$.
  have h_inter_order : Nat.card (↥((P : Subgroup G) ⊓ (Q : Subgroup G))) < Fintype.card α := by
    have h_inter_order : Nat.card (↥((P : Subgroup G) ⊓ (Q : Subgroup G))) < Nat.card P := by
      convert Set.ncard_lt_ncard h_inter_proper;
    have := sylow_card_eq_prime htrans hp P; aesop;
  -- Since $P$ and $Q$ are distinct Sylow $p$-subgroups, their intersection $P \cap Q$ is a proper subgroup of $P$, and hence has order less than $p$. Therefore, $P \cap Q$ must be trivial.
  have h_inter_trivial : Nat.card (↥((P : Subgroup G) ⊓ (Q : Subgroup G))) ∣ Fintype.card α := by
    convert Subgroup.card_dvd_of_le h_inter_proper.le;
    have := sylow_card_eq_prime htrans hp P; aesop;
  rw [ Nat.dvd_prime hp ] at h_inter_trivial;
  rw [ Subgroup.eq_bot_iff_card ];
  exact h_inter_trivial.resolve_right h_inter_order.ne

/-
PROBLEM
If a primitive subgroup of S_p contains a cycle of length 2 ≤ l ≤ p-2,
then it is 2-transitive (by Jordan's criterion).

PROVIDED SOLUTION
Since g is a cycle in G with support size s where 2 ≤ s, by `isPretransitive_of_isCycle_mem`, the fixing subgroup of (g.support : Set α)ᶜ acts pretransitively on SubMulAction.ofFixingSubgroup G (g.support : Set α)ᶜ.

The complement of g.support has ncard = Fintype.card α - s. We need to verify the conditions for `IsPreprimitive.is_two_pretransitive`:
- hG = hprim (G is primitive)
- s = (g.support : Set α)ᶜ (the set of fixed points of g)
- hsn : s.ncard = n + 1 where n + 2 < Nat.card α
  Here s.ncard = Fintype.card α - g.support.card, so n + 1 = p - s, n + 2 = p - s + 1.
  We need p - s + 1 < p, i.e., s ≥ 2. ✓ (given hlen)
  Also need s + 1 < p, i.e., s ≤ p - 2. ✓ (given hlen')
- hs_trans: the fixing subgroup acts transitively, from isPretransitive_of_isCycle_mem

Use Nat.card_eq_fintype_card to convert between Nat.card and Fintype.card when needed.
-/
lemma two_transitive_of_short_cycle
    {G : Subgroup (Equiv.Perm α)}
    (hp : (Fintype.card α).Prime)
    (hprim : IsPreprimitive G α)
    {g : Equiv.Perm α} (hg : g ∈ G) (hcyc : g.IsCycle)
    (hlen : 2 ≤ g.support.card) (hlen' : g.support.card + 1 < Fintype.card α) :
    IsMultiplyPretransitive G α 2 := by
  -- By the hypothesis `isPretransitive_of_isCycle_mem`, the fixing subgroup of (g.support : Set α)ᶜ acts pretransitively on SubMulAction.ofFixingSubgroup G (g.support : Set α)ᶜ.
  have h_subgroup_pretrans : IsPretransitive (↥(fixingSubgroup G (g.support : Set α)ᶜ)) (SubMulAction.ofFixingSubgroup G (g.support : Set α)ᶜ) := by
    exact?;
  apply_rules [ IsPreprimitive.is_two_pretransitive ];
  any_goals exact Fintype.card α - g.support.card - 1;
  · simp +decide [ Set.ncard_eq_toFinset_card' ];
    rw [ Finset.card_compl, tsub_add_cancel_of_le ];
    exact Nat.sub_pos_of_lt ( by linarith );
  · rw [ Nat.sub_sub ] ; rw [ Nat.card_eq_fintype_card ] ; omega;

/-
PROBLEM
If there are at least 2 Sylow p-subgroups, then n_p ≥ p + 1.

PROVIDED SOLUTION
¬ Subsingleton means Nat.card (Sylow p G) ≥ 2 (there exist two distinct elements). By card_sylow_modEq_one (haveI : Fact p.Prime := ⟨hp⟩), n_p ≡ 1 [MOD p]. Since n_p ≥ 2 and n_p ≡ 1 mod p with p ≥ 2, the smallest value ≥ 2 that's ≡ 1 mod p is p + 1. So n_p ≥ p + 1.
-/
lemma card_sylow_ge_prime_add_one
    {G : Subgroup (Equiv.Perm α)}
    (hp : (Fintype.card α).Prime)
    (hns : ¬ Subsingleton (Sylow (Fintype.card α) G)) :
    Fintype.card α + 1 ≤ Nat.card (Sylow (Fintype.card α) G) := by
  contrapose! hns; haveI := Fact.mk hp; simp_all +decide [ Nat.ModEq, Cardinal.mk_fintype ] ;
  -- Let's denote the number of Sylow p-subgroups by n_p. From hns, we have n_p ≤ p. But since n_p ≡ 1 mod p, the only possibility is n_p = 1.
  have hnp_one : Nat.card (Sylow (Fintype.card α) G) ≡ 1 [MOD Fintype.card α] := by
    haveI := Fact.mk hp; exact?;
  have := hnp_one.symm.dvd; simp_all +decide [ Nat.modEq_iff_dvd ] ;
  obtain ⟨ k, hk ⟩ := this; simp_all +decide [ sub_eq_iff_eq_add ] ;
  rcases lt_trichotomy k 0 with hk' | rfl | hk' <;> norm_num at * <;> try nlinarith [ hp.two_le ] ;
  exact Fintype.card_eq_one_iff.mp hk |> fun ⟨ x, hx ⟩ => ⟨ fun a b => by have := hx a; have := hx b; aesop ⟩ ;

/-
PROBLEM
n_p divides the index [G : P], which equals |stabilizer(a)| for transitive G.

PROVIDED SOLUTION
n_p = [G : N_G(P)] (by Sylow.card_eq_index_normalizer). The index of N_G(P) divides the index of P in G: [G : N_G(P)] divides [G : P] since P ≤ N_G(P).

[G : P] = Nat.card G / Nat.card P. By sylow_card_eq_prime, Nat.card P = Fintype.card α = p.

By orbit-stabilizer with transitivity: Nat.card G = Fintype.card α * Nat.card (stabilizer G a).
So [G : P] = Nat.card G / p = Nat.card (stabilizer G a).

Therefore n_p | Nat.card (stabilizer G a).
-/
lemma card_sylow_dvd_stabilizer
    {G : Subgroup (Equiv.Perm α)}
    (htrans : IsPretransitive G α) (hp : (Fintype.card α).Prime)
    (a : α) :
    Nat.card (Sylow (Fintype.card α) G) ∣ Nat.card (MulAction.stabilizer G a) := by
  -- By Sylow's theorems, the number of Sylow p-subgroups $n_p$ divides the index of a Sylow p-subgroup in $G$, which is $|G| / p$.
  have h_sylow_div : Nat.card (Sylow (Fintype.card α) G) ∣ Nat.card G / Fintype.card α := by
    haveI := Fact.mk hp;
    have h_sylow_div : Nat.card (Sylow (Fintype.card α) G) ∣ Nat.card (G ⧸ (Sylow.toSubgroup (Classical.arbitrary (Sylow (Fintype.card α) G)))) := by
      rw [ Nat.card_congr ( Sylow.equivQuotientNormalizer _ ) ];
      exact Subgroup.index_dvd_of_le ( Subgroup.le_normalizer );
    convert h_sylow_div using 1;
    rw [ Nat.div_eq_of_eq_mul_left ];
    · exact hp.pos;
    · have := Subgroup.card_eq_card_quotient_mul_card_subgroup ( Classical.arbitrary ( Sylow ( Fintype.card α ) G ) |> Sylow.toSubgroup );
      have := sylow_card_eq_prime htrans hp ( Classical.arbitrary ( Sylow ( Fintype.card α ) G ) ) ; aesop;
  -- Since $G$ acts transitively on $\alpha$, the index $[G : \mathrm{Stab}_G(a)]$ equals $|\alpha|$.
  have h_index : Nat.card G = Nat.card (stabilizer G a) * Fintype.card α := by
    have := Subgroup.card_mul_index ( MulAction.stabilizer G a );
    rw [ ← this, Subgroup.index_eq_card ];
    rw [ ← Nat.card_eq_fintype_card ];
    rw [ ← Nat.card_congr ( MulAction.orbitEquivQuotientStabilizer ( G ) a ) ];
    rw [ show ( orbit ( G ) a : Set α ) = Set.univ from Set.eq_univ_iff_forall.mpr fun x => by obtain ⟨ g, hg ⟩ := htrans.exists_smul_eq a x; aesop ] ; simp +decide [ Nat.card_eq_fintype_card ] ;
  rwa [ h_index, Nat.mul_div_cancel _ hp.pos ] at h_sylow_div

/-
PROBLEM
In a transitive group on p prime elements, if the Sylow p-subgroup is not unique,
then some non-identity element has at least 2 fixed points.

PROVIDED SOLUTION
Pick any a : α (exists since p ≥ 2).

By card_sylow_ge_prime_add_one, n_p ≥ p + 1.
By card_sylow_dvd_stabilizer, n_p | Nat.card (stabilizer G a).
So Nat.card (stabilizer G a) ≥ p + 1.

The stabilizer G_a fixes a and acts on α. Consider its action on α \ {a} which has p - 1 elements.
If G_a acted semiregularly (freely) on α \ {a} — meaning every non-identity element of G_a moves every point of α \ {a} — then for any b ∈ α \ {a}, the orbit of b under G_a would have size = |G_a| (since stabilizer of b in G_a is trivial). But orbits partition α \ {a} which has p - 1 elements, so |G_a| divides p - 1. But |G_a| ≥ p + 1 > p - 1 ≥ 1, so |G_a| cannot divide p - 1. Contradiction.

So G_a does NOT act freely on α \ {a}: ∃ g ∈ G_a, g ≠ 1, and ∃ b ∈ α \ {a} with g • b = b. Then g fixes a (since g ∈ G_a, meaning (g : Perm α) a = a) and g fixes b (g • b = b means (g : Perm α) b = b). So the set {x : α | (g : Perm α) x = x} contains both a and b (with a ≠ b), hence has card ≥ 2.

For orderOf g ≠ p: if orderOf (g : Perm α) = p, then by card_fixedBy_eq_zero_of_orderOf_eq_prime, g has 0 fixed points. But g has ≥ 2 fixed points. Contradiction.

To formalize the "free action" contradiction: Nat.card (stabilizer G a) > p - 1 = Fintype.card α - 1. If every non-identity element of stabilizer G a moved every point of α \ {a}, then the stabilizer of b in (stabilizer G a) would be ⊥ for each b ≠ a. By orbit-stabilizer for the action of (stabilizer G a) on α, the orbit of b has size = |stabilizer G a|. Since b ∈ α \ {a} and the orbits of (stabilizer G a) on α include {a} and the orbits on α \ {a}, each non-singleton orbit has size |stabilizer G a| ≥ p + 1 > p - 1 = |α \ {a}|. So there are no full orbits in α \ {a}, contradiction (the orbit of b is ≤ p - 1 but = |stabilizer G a| ≥ p + 1).
-/
lemma exists_two_fixedPoints_of_not_subsingleton_sylow
    {G : Subgroup (Equiv.Perm α)}
    (htrans : IsPretransitive G α) (hp : (Fintype.card α).Prime)
    (hns : ¬ Subsingleton (Sylow (Fintype.card α) G)) :
    ∃ g : G, g ≠ 1 ∧ 2 ≤ ((Finset.univ.filter (fun x : α => (g : Equiv.Perm α) x = x)).card) ∧
      ¬ orderOf (g : Equiv.Perm α) = Fintype.card α := by
  obtain ⟨g, hg_ne_one, hg_fixed⟩ : ∃ g : MulAction.stabilizer G (Classical.choose (Finset.card_pos.mp (Nat.Prime.pos hp))), g ≠ 1 ∧ ∃ b : α, b ≠ Classical.choose (Finset.card_pos.mp (Nat.Prime.pos hp)) ∧ (g : Equiv.Perm α) b = b := by
    -- By assumption, $|G_a| \geq p + 1$.
    have h_card_stabilizer : (Nat.card (MulAction.stabilizer G (Classical.choose (Finset.card_pos.mp (Nat.Prime.pos hp)))) : ℕ) ≥ Fintype.card α + 1 := by
      have := card_sylow_ge_prime_add_one hp hns;
      exact le_trans this ( card_sylow_dvd_stabilizer htrans hp _ |> Nat.le_of_dvd ( Nat.card_pos ) );
    -- If every non-identity element of $G_a$ moved every point of $\alpha \setminus \{a\}$, then the stabilizer of $b$ in $G_a$ would be $\bot$ for each $b \neq a$.
    by_contra h_contra
    push_neg at h_contra
    have h_free_action : ∀ g : MulAction.stabilizer G (Classical.choose (Finset.card_pos.mp (Nat.Prime.pos hp))), g ≠ 1 → ∀ b : α, b ≠ Classical.choose (Finset.card_pos.mp (Nat.Prime.pos hp)) → (g : Equiv.Perm α) b ≠ b := by
      exact h_contra;
    -- By orbit-stabilizer for the action of (stabilizer G a) on α, the orbit of b has size = |stabilizer G a|.
    have h_orbit_size : ∀ b : α, b ≠ Classical.choose (Finset.card_pos.mp (Nat.Prime.pos hp)) → (Nat.card (MulAction.orbit (MulAction.stabilizer G (Classical.choose (Finset.card_pos.mp (Nat.Prime.pos hp)))) b) : ℕ) = Nat.card (MulAction.stabilizer G (Classical.choose (Finset.card_pos.mp (Nat.Prime.pos hp)))) := by
      intro b hb_ne_a
      have h_orbit_size : (Nat.card (MulAction.orbit (MulAction.stabilizer G (Classical.choose (Finset.card_pos.mp (Nat.Prime.pos hp)))) b) : ℕ) = Nat.card (MulAction.stabilizer G (Classical.choose (Finset.card_pos.mp (Nat.Prime.pos hp)))) := by
        have h_free_action : ∀ g : MulAction.stabilizer G (Classical.choose (Finset.card_pos.mp (Nat.Prime.pos hp))), g ≠ 1 → (g : Equiv.Perm α) b ≠ b := by
          exact fun g hg => h_free_action g hg b hb_ne_a
        have h_free_action : ∀ g₁ g₂ : MulAction.stabilizer G (Classical.choose (Finset.card_pos.mp (Nat.Prime.pos hp))), (g₁ : Equiv.Perm α) b = (g₂ : Equiv.Perm α) b → g₁ = g₂ := by
          intro g₁ g₂ h_eq
          have h_eq' : (g₁⁻¹ * g₂ : Equiv.Perm α) b = b := by
            simp +decide [ h_eq ];
            rw [ ← h_eq, Equiv.symm_apply_apply ];
          specialize h_free_action ( g₁⁻¹ * g₂ ) ; simp_all +decide [ mul_eq_one_iff_eq_inv ] ;
        apply Nat.card_congr;
        symm;
        refine' Equiv.ofBijective ( fun g => ⟨ _, MulAction.mem_orbit _ _ ⟩ ) ⟨ fun g₁ g₂ h => _, fun x => _ ⟩;
        exact g;
        · exact h_free_action g₁ g₂ ( by simpa using congr_arg Subtype.val h );
        · rcases x with ⟨ x, hx ⟩ ; rcases hx with ⟨ g, rfl ⟩ ; exact ⟨ g, rfl ⟩ ;
      exact h_orbit_size;
    -- Since the orbit of b has size = |stabilizer G a| and |stabilizer G a| ≥ p + 1, the orbit of b must contain at least p + 1 elements.
    have h_orbit_card : ∀ b : α, b ≠ Classical.choose (Finset.card_pos.mp (Nat.Prime.pos hp)) → (Nat.card (MulAction.orbit (MulAction.stabilizer G (Classical.choose (Finset.card_pos.mp (Nat.Prime.pos hp)))) b) : ℕ) ≥ Fintype.card α + 1 := by
      exact fun b hb => h_orbit_size b hb ▸ h_card_stabilizer;
    exact absurd ( h_orbit_card ( Classical.choose ( Finset.exists_mem_ne ( show 1 < Fintype.card α from hp.one_lt ) ( Classical.choose ( Finset.card_pos.mp ( Nat.Prime.pos hp ) ) ) ) ) ( Classical.choose_spec ( Finset.exists_mem_ne ( show 1 < Fintype.card α from hp.one_lt ) ( Classical.choose ( Finset.card_pos.mp ( Nat.Prime.pos hp ) ) ) ) |>.2 ) ) ( not_le_of_gt ( lt_of_le_of_lt ( Set.ncard_le_ncard ( show ( MulAction.orbit ( MulAction.stabilizer G ( Classical.choose ( Finset.card_pos.mp ( Nat.Prime.pos hp ) ) ) ) _ ) ⊆ Set.univ from Set.subset_univ _ ) ) ( by simp +decide [ Set.ncard_univ ] ) ) );
  refine' ⟨ g, _, _, _ ⟩ <;> simp_all +decide [ Finset.card_pos ];
  · obtain ⟨ b, hb₁, hb₂ ⟩ := hg_fixed; exact Finset.one_lt_card.2 ⟨ Classical.choose ( Finset.card_pos.mp ( Nat.Prime.pos hp ) ), by aesop, b, by aesop ⟩ ;
  · obtain ⟨ b, hb_ne, hb_fixed ⟩ := hg_fixed
    by_contra h_contra
    have h_fixed_points : Fintype.card (MulAction.fixedBy α (g : Equiv.Perm α)) ≥ 2 := by
      refine' Fintype.one_lt_card_iff_nontrivial.mpr _;
      refine' ⟨ ⟨ b, hb_fixed ⟩, ⟨ Classical.choose ( Finset.card_pos.mp ( Nat.Prime.pos hp ) ), _ ⟩, _ ⟩ <;> simp_all +decide [ fixedBy ];
      exact g.2
    have h_fixed_points_zero : Fintype.card (MulAction.fixedBy α (g : Equiv.Perm α)) = 0 := by
      convert card_fixedBy_eq_zero_of_orderOf_eq_prime hp _ _;
      convert h_contra using 1;
      simp +decide [ orderOf_eq_orderOf_iff ]
    linarith [h_fixed_points, h_fixed_points_zero]

/-- In a primitive group on p ≥ 5 elements, if a non-identity element fixes at least 2
points and has prime order q ≠ p, then G contains a cycle of length between 2 and p-2.

This is the key cycle extraction lemma used in the proof of Burnside's theorem.
The proof uses the fact that in a primitive group, the support of a non-identity element
with proper support is NOT a block. By the minimal counterexample argument (choosing
an element of minimal support among non-identity elements with proper support),
primitivity forces this minimal element to be a single cycle. If it were a product of
≥ 2 disjoint cycles, one could use the non-block property to find a conjugate whose
product with the original has strictly smaller support, contradicting minimality.
-/
lemma exists_short_cycle_of_prime_order_element
    {G : Subgroup (Equiv.Perm α)}
    (hp : (Fintype.card α).Prime)
    (h5 : 5 ≤ Fintype.card α)
    (hprim : IsPreprimitive G α)
    (g : Equiv.Perm α) (hg : g ∈ G) (hg_ne : g ≠ 1)
    (hfix : 2 ≤ (Finset.univ.filter (fun x : α => g x = x)).card)
    (hord_ne : ¬ orderOf g = Fintype.card α) :
    ∃ c : Equiv.Perm α, c ∈ G ∧ c.IsCycle ∧ 2 ≤ c.support.card ∧
      c.support.card + 1 < Fintype.card α := by
  sorry

/-
PROBLEM
If G is transitive on p elements (p prime) and NOT 2-transitive,
then the Sylow p-subgroup is unique (hence normal).

PROVIDED SOLUTION
By contradiction: assume ¬ Subsingleton (Sylow p G). We show G is 2-transitive, contradicting h2.

Case on whether Fintype.card α ≤ 3:

If Fintype.card α = 2: G is 2-transitive on 2 elements (every transitive group on 2 elements is 2-transitive). Contradiction with h2. To show: a transitive group on 2 elements acts 2-transitively. Use is_two_pretransitive_iff: for any distinct a ≠ b and c ≠ d, find g with g • a = c, g • b = d. Since |α| = 2, the only pairs are (a,b) and (b,a). Use transitivity to find the necessary element.

If Fintype.card α = 3: since 3 is prime, ¬ Subsingleton means n_3 ≥ 4 (n_3 ≡ 1 mod 3, n_3 > 1). Each Sylow 3-subgroup has 2 elements of order 3 (which are 3-cycles). With n_3 ≥ 4 Sylow subgroups, there are ≥ 8 elements of order 3. But |G| divides 3! = 6, so |G| ≤ 6. But 8 < |G| is impossible since |G| ≤ 6 and we need at least 8 non-identity elements. So ¬ Subsingleton is impossible for p = 3. Contradiction.

If Fintype.card α ≥ 5: By exists_two_fixedPoints_of_not_subsingleton_sylow, there exists g : G, g ≠ 1 with ≥ 2 fixed points. G is primitive (IsPreprimitive.of_prime_card, converting Fintype.card to Nat.card). By exists_short_cycle_of_prime_order_element, G contains a cycle c with 2 ≤ c.support.card and c.support.card + 1 < Fintype.card α. By two_transitive_of_short_cycle, G is 2-transitive. Contradiction with h2.
-/
lemma subsingleton_sylow_of_not_two_transitive
    {G : Subgroup (Equiv.Perm α)}
    (htrans : IsPretransitive G α) (hp : (Fintype.card α).Prime)
    (h2 : ¬ IsMultiplyPretransitive G α 2) :
    Subsingleton (Sylow (Fintype.card α) G) := by
  by_contra h_contra
  obtain ⟨g, hg_ne, hg_fixed⟩ := exists_two_fixedPoints_of_not_subsingleton_sylow htrans hp h_contra;
  by_cases h5 : 5 ≤ Fintype.card α;
  · have h_cycle : ∃ c : Equiv.Perm α, c ∈ G ∧ c.IsCycle ∧ 2 ≤ c.support.card ∧ c.support.card + 1 < Fintype.card α := by
      have h_primitive : IsPreprimitive G α := by
        have h_prime : Nat.Prime (Nat.card α) := by
          rwa [ Nat.card_eq_fintype_card ]
        exact IsPreprimitive.of_prime_card h_prime;
      convert exists_short_cycle_of_prime_order_element hp h5 h_primitive g g.2 _ _ _ <;> aesop;
    obtain ⟨ c, hc₁, hc₂, hc₃, hc₄ ⟩ := h_cycle;
    apply h2;
    apply two_transitive_of_short_cycle hp (IsPreprimitive.of_prime_card (by
    rwa [ Nat.card_eq_fintype_card ])) hc₁ hc₂ hc₃ hc₄;
  · interval_cases _ : Fintype.card α <;> simp_all +decide only [IsPretransitive];
    · -- Since $g$ fixes at least two elements, it must be the identity permutation.
      have hg_id : (g : Equiv.Perm α) = 1 := by
        have := Finset.eq_of_subset_of_card_le ( show Finset.filter ( fun x => ( g : Equiv.Perm α ) x = x ) Finset.univ ⊆ Finset.univ from Finset.filter_subset _ _ ) ; simp_all +decide ;
        exact hg_ne ( Subtype.ext <| Equiv.Perm.ext this );
      exact hg_ne ( Subtype.ext hg_id );
    · -- Since $g$ fixes at least two elements, it must be the identity permutation.
      have hg_id : (g : Equiv.Perm α) = 1 := by
        have hg_id : ∀ x : α, (g : Equiv.Perm α) x = x := by
          have := Finset.card_add_card_compl ( Finset.filter ( fun x => ( g : Equiv.Perm α ) x = x ) Finset.univ ) ; simp_all +decide ;
          have : Finset.card ( Finset.filter ( fun x => ¬ ( g : Equiv.Perm α ) x = x ) Finset.univ ) ≤ 1 := by linarith; ; interval_cases _ : Finset.card ( Finset.filter ( fun x => ¬ ( g : Equiv.Perm α ) x = x ) Finset.univ ) <;> simp_all +decide ;
          obtain ⟨ x, hx ⟩ := Finset.card_eq_one.mp ‹_›; simp_all +decide [ Finset.ext_iff ] ;
          have := hx x; have := hx ( g.val x ) ; simp_all +decide [ Equiv.Perm.ext_iff ] ;
          grind +ring;
        exact Equiv.Perm.ext hg_id;
      exact hg_ne ( Subtype.ext hg_id )

/-! ## Main theorem -/

/--
**Burnside's theorem on transitive permutation groups of prime degree**.

A transitive permutation group of prime degree is either 2-transitive or has a normal regular
subgroup.
-/
theorem MainTheorem
    {α : Type*} [Fintype α]
    {G : Subgroup (Equiv.Perm α)}
    (htrans : IsPretransitive G α)
    (hp : (Fintype.card α).Prime) :
    IsMultiplyPretransitive G α 2 ∨
      ∃ N : Subgroup G, N.Normal ∧ IsPretransitive N α ∧
        ∀ a : α, MulAction.stabilizer N a = ⊥ := by
  classical
  by_cases h2 : IsMultiplyPretransitive G α 2
  · exact Or.inl h2
  · right
    have huniq := subsingleton_sylow_of_not_two_transitive htrans hp h2
    haveI : Fact (Fintype.card α).Prime := ⟨hp⟩
    let P : Sylow (Fintype.card α) G := default
    have hPnorm : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
    have hPcard : Nat.card P = Fintype.card α := sylow_card_eq_prime htrans hp P
    have hPtrans : IsPretransitive P α := pretransitive_of_prime_card hp hPcard
    have hPstab : ∀ a : α, MulAction.stabilizer P a = ⊥ :=
      stabilizer_eq_bot_of_prime_card hp hPcard hPtrans
    exact ⟨P, hPnorm, hPtrans, hPstab⟩

end BurnsidePrimeDegreeTheorem