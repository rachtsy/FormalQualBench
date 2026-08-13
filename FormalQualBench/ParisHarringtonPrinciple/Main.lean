import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Order.KonigLemma
import Mathlib.Order.Interval.Finset.Nat

namespace ParisHarringtonPrinciple

open Finset

/-- A subset `H` of `[1, N]` is relatively large for the Paris-Harrington principle if it has at
least `m` elements and its cardinality is at least its minimum element. -/
def RelativelyLarge (m N : ℕ) (H : Finset ℕ) : Prop :=
  H ⊆ Finset.Ico 1 (N + 1) ∧
  m ≤ H.card ∧
  ∃ hne : H.Nonempty, H.min' hne ≤ H.card

/-- A set `H` is homogeneous for a coloring if all `k`-subsets of `H` have the same color. -/
def IsHomogeneous {α β : Type*} [DecidableEq α] (k : ℕ) (H : Finset α)
    (c : Finset α → β) : Prop :=
  ∀ s ∈ H.powersetCard k, ∀ t ∈ H.powersetCard k, c s = c t

/-
The following infinite Ramsey proof is adapted from Yann Pequignot's
`lean-infinite-ramsey` formalization:
Copyright (c) 2026 Yann Pequignot. Released under the Apache License 2.0.
-/

theorem exists_infinite_fiber_nat {κ : Type*} [Finite κ] (f : ℕ → κ) :
    ∃ k : κ, {n : ℕ | f n = k}.Infinite := by
  obtain ⟨k, hk⟩ := Finite.exists_infinite_fiber f
  exact ⟨k, Set.infinite_coe_iff.mp hk⟩

structure RamseyState {κ : Type*} (c : Finset ℕ → κ) (r : ℕ) where
  vert : ℕ
  col : κ
  succ : Set ℕ
  hInf : succ.Infinite
  hgt : ∀ x ∈ succ, vert < x
  hprop : ∀ t : Finset ℕ, ↑t ⊆ succ → t.card = r → c (insert vert t) = col

theorem infinite_ramsey {κ : Type*} [Finite κ] (r : ℕ) (c : Finset ℕ → κ)
    {M : Set ℕ} (hM : M.Infinite) :
    ∃ N ⊆ M, N.Infinite ∧ ∃ col : κ,
      ∀ t : Finset ℕ, ↑t ⊆ N → t.card = r → c t = col := by
  induction r generalizing c M with
  | zero =>
    refine ⟨M, subset_rfl, hM, c ∅, fun t _ ht ↦ ?_⟩
    rw [Finset.card_eq_zero.mp ht]
  | succ r ih =>
    have stepCore : ∀ S : Set ℕ, S.Infinite →
        ∃ a' ∈ S, ∃ (col' : κ) (N : Set ℕ),
          N.Infinite ∧ N ⊆ S ∧ (∀ x ∈ N, a' < x) ∧
          ∀ t : Finset ℕ, ↑t ⊆ N → t.card = r → c (insert a' t) = col' := by
      intro S hS
      refine ⟨sInf S, Nat.sInf_mem hS.nonempty, ?_⟩
      have hle : ∀ x ∈ S, sInf S ≤ x := fun x hx ↦ Nat.sInf_le hx
      have hdiff : (S \ {sInf S}).Infinite := hS.diff (Set.finite_singleton _)
      obtain ⟨N, hNsub, hNinf, col', hmono⟩ := ih (fun e ↦ c (insert (sInf S) e)) hdiff
      refine ⟨col', N, hNinf, hNsub.trans Set.diff_subset, ?_, hmono⟩
      intro x hxN
      have hxd := hNsub hxN
      exact lt_of_le_of_ne (hle x hxd.1) fun h ↦ hxd.2 (h ▸ rfl)
    have advance : ∀ s : RamseyState c r, ∃ s' : RamseyState c r,
        s'.vert ∈ s.succ ∧ s'.succ ⊆ s.succ := by
      intro s
      obtain ⟨a', ha'mem, col', N, hNinf, hNsub, hNgt, hNprop⟩ := stepCore s.succ s.hInf
      exact ⟨⟨a', col', N, hNinf, hNgt, hNprop⟩, ha'mem, hNsub⟩
    obtain ⟨a₀, ha₀M, col₀, N₀, hN₀inf, hN₀sub, hN₀gt, hN₀prop⟩ := stepCore M hM
    let s₀ : RamseyState c r := ⟨a₀, col₀, N₀, hN₀inf, hN₀gt, hN₀prop⟩
    let states : ℕ → RamseyState c r := fun n ↦ n.rec s₀ fun _ s ↦ (advance s).choose
    have I1 : ∀ n, (states (n + 1)).vert ∈ (states n).succ :=
      fun n ↦ (advance (states n)).choose_spec.1
    have I2 : ∀ n, (states (n + 1)).succ ⊆ (states n).succ :=
      fun n ↦ (advance (states n)).choose_spec.2
    have I3 : ∀ n, (states n).vert < (states (n + 1)).vert :=
      fun n ↦ (states n).hgt _ (I1 n)
    have I4 : ∀ m n, m ≤ n → (states n).succ ⊆ (states m).succ := by
      intro m n hmn
      induction n with
      | zero => simp [Nat.le_zero.mp hmn]
      | succ n ih2 =>
        rcases Nat.lt_or_eq_of_le hmn with h | rfl
        · exact (I2 n).trans (ih2 (Nat.lt_succ_iff.mp h))
        · exact subset_rfl
    have I5 : ∀ m n, m < n → (states n).vert ∈ (states m).succ := by
      intro m n hmn
      cases n with
      | zero => exact absurd hmn (Nat.not_lt_zero m)
      | succ n => exact I4 m n (Nat.lt_succ_iff.mp hmn) (I1 n)
    have vmono : StrictMono fun n ↦ (states n).vert := strictMono_nat_of_lt_succ I3
    have hsuccM : ∀ n, (states n).succ ⊆ M := fun n ↦ (I4 0 n (Nat.zero_le n)).trans hN₀sub
    have hvertM : ∀ n, (states n).vert ∈ M := by
      intro n
      cases n with
      | zero => exact ha₀M
      | succ n => exact hsuccM n (I1 n)
    obtain ⟨col, hJinf⟩ := exists_infinite_fiber_nat (fun n ↦ (states n).col)
    set V : ℕ → ℕ := fun n ↦ (states n).vert with hV
    set J : Set ℕ := {n | (states n).col = col} with hJ
    refine ⟨V '' J, ?_, hJinf.image (vmono.injective.injOn), col, ?_⟩
    · rintro x ⟨n, _, rfl⟩
      exact hvertM n
    · intro t htN htcard
      have ht_ne : t.Nonempty := Finset.card_pos.mp (by rw [htcard]; exact Nat.succ_pos r)
      set a := t.min' ht_ne with ha
      have ha_mem : a ∈ t := Finset.min'_mem _ _
      obtain ⟨m, hmJ, hVm⟩ : ∃ m, (states m).col = col ∧ (states m).vert = a := by
        obtain ⟨m, hmJ, hVm⟩ := htN (Finset.mem_coe.mpr ha_mem)
        exact ⟨m, hmJ, hVm⟩
      have hsub : ↑(t.erase a) ⊆ (states m).succ := by
        intro x hx
        rw [Finset.mem_coe, Finset.mem_erase] at hx
        obtain ⟨hxne, hxt⟩ := hx
        obtain ⟨p, hpJ, hVp⟩ := htN (Finset.mem_coe.mpr hxt)
        have hax : a < x := lt_of_le_of_ne (Finset.min'_le t x hxt) (Ne.symm hxne)
        have hmp : m < p := by
          have h1 : (states m).vert < (states p).vert := by
            rw [hVm, show (states p).vert = x from hVp]
            exact hax
          exact vmono.lt_iff_lt.mp h1
        have := I5 m p hmp
        rwa [show (states p).vert = x from hVp] at this
      have hcard : (t.erase a).card = r := by
        rw [Finset.card_erase_of_mem ha_mem, htcard]
        omega
      have key := (states m).hprop (t.erase a) hsub hcard
      rw [hVm, Finset.insert_erase ha_mem, hmJ] at key
      exact key

def positiveEmbedding (N : ℕ) : Fin N ↪ ℕ where
  toFun x := x + 1
  inj' := by
    intro x y hxy
    exact Fin.ext (Nat.add_right_cancel hxy)

def IsGoodColoringSet (k m N r : ℕ) (c : Finset (Fin N) → Fin r)
    (H : Finset (Fin N)) : Prop :=
  m ≤ H.card ∧
  (∃ x ∈ H, x.val + 1 ≤ H.card) ∧
  IsHomogeneous k H c

def IsBadColoring (k m N r : ℕ) (c : Finset (Fin N) → Fin r) : Prop :=
  ∀ H, ¬IsGoodColoringSet k m N r c H

abbrev BadColoring (k m N r : ℕ) :=
  {c : Finset (Fin N) → Fin r // IsBadColoring k m N r c}

theorem isHomogeneous_map_iff {α β κ : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (k : ℕ) (H : Finset α) (c : Finset β → κ) :
    IsHomogeneous k (H.map e) c ↔ IsHomogeneous k H (fun s ↦ c (s.map e)) := by
  rw [IsHomogeneous, IsHomogeneous, Finset.powersetCard_map]
  constructor
  · intro h s hs t ht
    exact h (s.map e) (Finset.mem_map_of_mem _ hs) (t.map e) (Finset.mem_map_of_mem _ ht)
  · intro h s hs t ht
    obtain ⟨s', hs', rfl⟩ := Finset.mem_map.mp hs
    obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
    exact h s' hs' t' ht'

def BadColoring.restrict {k m r i j : ℕ} (hij : i ≤ j)
    (c : BadColoring k m j r) : BadColoring k m i r := by
  refine ⟨fun s ↦ c.1 (s.map (Fin.castLEEmb hij)), ?_⟩
  intro H hgood
  apply c.2 (H.map (Fin.castLEEmb hij))
  refine ⟨by simpa using hgood.1, ?_, ?_⟩
  · obtain ⟨x, hxH, hx⟩ := hgood.2.1
    exact ⟨Fin.castLE hij x, Finset.mem_map_of_mem _ hxH, by simpa using hx⟩
  · exact (isHomogeneous_map_iff (Fin.castLEEmb hij) k H c.1).2 hgood.2.2

theorem BadColoring.restrict_refl {k m r N : ℕ} (c : BadColoring k m N r) :
    c.restrict (le_refl N) = c := by
  apply Subtype.ext
  funext s
  change c.1 (s.map (Fin.castLEEmb (le_refl N))) = c.1 s
  rw [show s.map (Fin.castLEEmb (le_refl N)) = s by ext x; simp]

theorem BadColoring.restrict_trans {k m r i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l)
    (c : BadColoring k m l r) :
    (c.restrict hjl).restrict hij = c.restrict (hij.trans hjl) := by
  apply Subtype.ext
  funext s
  change c.1 ((s.map (Fin.castLEEmb hij)).map (Fin.castLEEmb hjl)) =
    c.1 (s.map (Fin.castLEEmb (hij.trans hjl)))
  rw [show (s.map (Fin.castLEEmb hij)).map (Fin.castLEEmb hjl) =
      s.map (Fin.castLEEmb (hij.trans hjl)) by ext x; simp]

theorem exists_uniform_good_bound (k r m : ℕ) (_hr : 0 < r) (_hm : k ≤ m) :
    ∃ N : ℕ, ∀ c : Finset (Fin N) → Fin r, ∃ H, IsGoodColoringSet k m N r c H := by
  by_contra hno
  push_neg at hno
  have hbad : ∀ N, Nonempty (BadColoring k m N r) := by
    intro N
    obtain ⟨c, hc⟩ := hno N
    exact ⟨⟨c, hc⟩⟩
  let π : {i j : ℕ} → (hij : i ≤ j) → BadColoring k m j r → BadColoring k m i r :=
    fun hij c ↦ c.restrict hij
  have π_refl : ∀ ⦃i⦄ (c : BadColoring k m i r), π (le_refl i) c = c := by
    intro i c
    exact BadColoring.restrict_refl c
  have π_trans : ∀ ⦃i j l⦄ (hij : i ≤ j) (hjl : j ≤ l) (c : BadColoring k m l r),
      π hij (π hjl c) = π (hij.trans hjl) c := by
    intro i j l hij hjl c
    exact BadColoring.restrict_trans hij hjl c
  have hfin : ∀ i c, {d : BadColoring k m (i + 1) r |
      π (Nat.le_add_right i 1) d = c}.Finite := by
    intro i c
    exact Set.toFinite _
  obtain ⟨bad, hbadcompat⟩ :=
    exists_seq_forall_proj_of_forall_finite π π_refl π_trans hfin
  let cInf : Finset ℕ → Fin r := fun s ↦
    (bad (s.sup id + 1)).1
      (s.attachFin (fun x hx ↦
        (show x ≤ s.sup id from Finset.le_sup (f := id) hx).trans_lt (Nat.lt_succ_self _)))
  obtain ⟨S, -, hS, col, hmono⟩ :=
    infinite_ramsey k cInf (M := Set.univ) Set.infinite_univ
  obtain ⟨a, haS⟩ := hS.nonempty
  let q := max m (a + 1)
  have hexT := @Set.Infinite.exists_superset_ncard_eq ℕ {a} S hS
    (Set.singleton_subset_iff.mpr haS) (Set.finite_singleton a) q (by simp [q])
  choose T haT hTsub hTcard using hexT
  have hTfin : T.Finite := by
    apply Set.finite_of_ncard_ne_zero
    rw [hTcard]
    simp [q]
  let H : Finset ℕ := hTfin.toFinset
  have hHcard : H.card = q := by
    simpa [H] using (Set.ncard_eq_toFinset_card T hTfin).symm.trans hTcard
  have hHne : H.Nonempty := by
    rw [← Finset.card_pos, hHcard]
    omega
  let N := H.max' hHne + 1
  have hHlt : ∀ x ∈ H, x < N := fun x hx ↦
    (Finset.le_max' H x hx).trans_lt (Nat.lt_succ_self _)
  let H₀ : Finset (Fin N) := H.attachFin hHlt
  have hH₀card : H₀.card = q := by simpa [H₀] using hHcard
  have hrel : ∃ x ∈ H₀, x.val + 1 ≤ H₀.card := by
    have haH : a ∈ H := hTfin.mem_toFinset.mpr (haT (Set.mem_singleton a))
    exact ⟨⟨a, hHlt a haH⟩, (Finset.mem_attachFin hHlt).mpr haH, by
      rw [hH₀card]
      exact le_max_right _ _⟩
  have hH₀hom : IsHomogeneous k H₀ (bad N).1 := by
    intro s hs t ht
    rw [Finset.mem_powersetCard] at hs ht
    let sNat := s.map Fin.valEmbedding
    let tNat := t.map Fin.valEmbedding
    have hsNatH : sNat ⊆ H := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact (Finset.mem_attachFin hHlt).mp (hs.1 hy)
    have htNatH : tNat ⊆ H := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact (Finset.mem_attachFin hHlt).mp (ht.1 hy)
    have hsNatCard : sNat.card = k := by simpa [sNat] using hs.2
    have htNatCard : tNat.card = k := by simpa [tNat] using ht.2
    have hsMono := hmono sNat
      (fun x hx ↦ hTsub (hTfin.mem_toFinset.mp (hsNatH hx))) hsNatCard
    have htMono := hmono tNat
      (fun x hx ↦ hTsub (hTfin.mem_toFinset.mp (htNatH hx))) htNatCard
    have hsBound : sNat.sup id + 1 ≤ N := by
      have hsMax : sNat.sup id ≤ H.max' hHne := by
        exact Finset.sup_le fun x hx ↦ Finset.le_max' H x (hsNatH hx)
      omega
    have htBound : tNat.sup id + 1 ≤ N := by
      have htMax : tNat.sup id ≤ H.max' hHne := by
        exact Finset.sup_le fun x hx ↦ Finset.le_max' H x (htNatH hx)
      omega
    have hsCompat := congrArg Subtype.val (hbadcompat hsBound)
    have htCompat := congrArg Subtype.val (hbadcompat htBound)
    have hsCast : (sNat.attachFin fun x hx ↦
        (show x ≤ sNat.sup id from Finset.le_sup (f := id) hx).trans_lt
          (Nat.lt_succ_self _)).map
          (Fin.castLEEmb hsBound) = s := by
      ext x
      constructor
      · intro hx
        obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hx
        have hyNat : (y : ℕ) ∈ sNat := (Finset.mem_attachFin _).mp hy
        obtain ⟨z, hz, hzy⟩ := Finset.mem_map.mp hyNat
        have hzx : z = x := by
          apply Fin.ext
          exact hzy.trans (congrArg Fin.val hyx)
        simpa [hzx] using hz
      · intro hx
        have hxNat : (x : ℕ) ∈ sNat := Finset.mem_map.mpr ⟨x, hx, rfl⟩
        let y : Fin (sNat.sup id + 1) := ⟨x, (show x ≤ sNat.sup id from
          Finset.le_sup (f := id) hxNat).trans_lt (Nat.lt_succ_self _)⟩
        exact Finset.mem_map.mpr ⟨y, (Finset.mem_attachFin _).mpr hxNat, Fin.ext rfl⟩
    have htCast : (tNat.attachFin fun x hx ↦
        (show x ≤ tNat.sup id from Finset.le_sup (f := id) hx).trans_lt
          (Nat.lt_succ_self _)).map
          (Fin.castLEEmb htBound) = t := by
      ext x
      constructor
      · intro hx
        obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hx
        have hyNat : (y : ℕ) ∈ tNat := (Finset.mem_attachFin _).mp hy
        obtain ⟨z, hz, hzy⟩ := Finset.mem_map.mp hyNat
        have hzx : z = x := by
          apply Fin.ext
          exact hzy.trans (congrArg Fin.val hyx)
        simpa [hzx] using hz
      · intro hx
        have hxNat : (x : ℕ) ∈ tNat := Finset.mem_map.mpr ⟨x, hx, rfl⟩
        let y : Fin (tNat.sup id + 1) := ⟨x, (show x ≤ tNat.sup id from
          Finset.le_sup (f := id) hxNat).trans_lt (Nat.lt_succ_self _)⟩
        exact Finset.mem_map.mpr ⟨y, (Finset.mem_attachFin _).mpr hxNat, Fin.ext rfl⟩
    have hsEq : cInf sNat = (bad N).1 s := by
      simp only [cInf]
      rw [← hsCast]
      exact (congrFun hsCompat _).symm
    have htEq : cInf tNat = (bad N).1 t := by
      simp only [cInf]
      rw [← htCast]
      exact (congrFun htCompat _).symm
    exact hsEq ▸ htEq ▸ hsMono.trans htMono.symm
  exact (bad N).2 H₀ ⟨by rw [hH₀card]; exact le_max_left _ _, hrel, hH₀hom⟩

/-- Paris-Harrington principle (strengthened finite Ramsey theorem): assuming `0 < r` and `k ≤ m`,
there exists `N` such that every `r`-coloring of the `k`-subsets of `[1, N]` has a relatively
large homogeneous set. This is the finite combinatorial statement whose unprovability over Peano
arithmetic is usually called the Paris-Harrington theorem. -/
theorem MainTheorem (k r m : ℕ) (hr : 0 < r) (hm : k ≤ m) :
    ∃ N : ℕ, ∀ (c : Finset ℕ → Fin r),
      ∃ H : Finset ℕ, RelativelyLarge m N H ∧ IsHomogeneous k H c := by
  obtain ⟨N, hN⟩ := exists_uniform_good_bound k r m hr hm
  refine ⟨N, fun c ↦ ?_⟩
  obtain ⟨H₀, hmH₀, hrel, hhom⟩ :=
    hN (fun s ↦ c (s.map (positiveEmbedding N)))
  let H : Finset ℕ := H₀.map (positiveEmbedding N)
  refine ⟨H, ?_, (isHomogeneous_map_iff (positiveEmbedding N) k H₀ c).2 hhom⟩
  refine ⟨?_, by simpa [H] using hmH₀, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_Ico.mpr ⟨by simp [positiveEmbedding], by
      simp only [positiveEmbedding]
      exact Nat.add_lt_add_right y.isLt 1⟩
  · obtain ⟨x, hxH₀, hx⟩ := hrel
    have hHne : H.Nonempty := ⟨positiveEmbedding N x, Finset.mem_map_of_mem _ hxH₀⟩
    refine ⟨hHne, (Finset.min'_le H (positiveEmbedding N x)
      (Finset.mem_map_of_mem _ hxH₀)).trans ?_⟩
    simpa [H, positiveEmbedding] using hx

end ParisHarringtonPrinciple
