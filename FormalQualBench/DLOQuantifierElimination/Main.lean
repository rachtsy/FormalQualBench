import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Complexity

namespace DLOQuantifierElimination

open FirstOrder Language

/-- A theory T eliminates quantifiers if every formula is semantically equivalent
to a quantifier-free formula in all models of T. -/
def EliminatesQuantifiers {L : Language} (T : L.Theory) : Prop :=
  ∀ {α : Type*} {n : ℕ} (φ : L.BoundedFormula α n),
    ∃ ψ : L.BoundedFormula α n,
      ψ.IsQF ∧
      ∀ (M : Type*) [L.Structure M] [M ⊨ T],
        ∀ (v : α → M) (xs : Fin n → M),
          φ.Realize v xs ↔ ψ.Realize v xs

private theorem realize_iff_of_fgequiv
    {M N : Type*} [Language.order.Structure M] [Language.order.Structure N]
    (hMN : Language.order.IsExtensionPair M N)
    (hNM : Language.order.IsExtensionPair N M)
    {α : Type*} {n : ℕ} (φ : Language.order.BoundedFormula α n)
    (f : Language.order.FGEquiv M N)
    (v : α → f.1.dom) (xs : Fin n → f.1.dom) :
    φ.Realize ((fun z : f.1.dom ↦ (z : M)) ∘ v)
        ((fun z : f.1.dom ↦ (z : M)) ∘ xs) ↔
      φ.Realize ((fun z : f.1.cod ↦ (z : N)) ∘ f.1.toEquiv ∘ v)
        ((fun z : f.1.cod ↦ (z : N)) ∘ f.1.toEquiv ∘ xs) := by
  induction φ generalizing f with
  | falsum => rfl
  | equal t₁ t₂ =>
      have hM := (BoundedFormula.IsAtomic.equal t₁ t₂).isQF.realize_embedding
        (Substructure.subtype f.1.dom) (v := v) (xs := xs)
      have hN := (BoundedFormula.IsAtomic.equal t₁ t₂).isQF.realize_embedding
        f.1.toEmbedding (v := v) (xs := xs)
      simpa only [Function.comp_def, PartialEquiv.toEmbedding_apply] using hM.trans hN.symm
  | rel R ts =>
      have hM := (BoundedFormula.IsAtomic.rel R ts).isQF.realize_embedding
        (Substructure.subtype f.1.dom) (v := v) (xs := xs)
      have hN := (BoundedFormula.IsAtomic.rel R ts).isQF.realize_embedding
        f.1.toEmbedding (v := v) (xs := xs)
      simpa only [Function.comp_def, PartialEquiv.toEmbedding_apply] using hM.trans hN.symm
  | imp φ ψ ihφ ihψ =>
      simpa only [BoundedFormula.realize_imp] using
        imp_congr (ihφ f v xs) (ihψ f v xs)
  | @all k θ ih =>
      simp only [BoundedFormula.realize_all]
      constructor
      · intro h (a : N)
        obtain ⟨g, ha, hfg⟩ := hNM.cod f a
        let v' : _ → g.1.dom :=
          Substructure.inclusion (PartialEquiv.dom_le_dom hfg) ∘ v
        let xs' : Fin k → g.1.dom :=
          Substructure.inclusion (PartialEquiv.dom_le_dom hfg) ∘ xs
        let b : g.1.dom := g.1.toEquiv.symm ⟨a, ha⟩
        have hleft :
            θ.Realize ((fun z : g.1.dom ↦ (z : M)) ∘ v')
              ((fun z : g.1.dom ↦ (z : M)) ∘ Fin.snoc xs' b) := by
          rw [Fin.comp_snoc]
          simpa [v', xs', Function.comp_def] using h (b : M)
        have hright := (ih g v' (Fin.snoc xs' b)).mp hleft
        rw [Fin.comp_snoc] at hright
        have hv :
            ((fun z : g.1.cod ↦ (z : N)) ∘ g.1.toEquiv ∘ v') =
              ((fun z : f.1.cod ↦ (z : N)) ∘ f.1.toEquiv ∘ v) := by
          funext x
          exact congrArg Subtype.val (PartialEquiv.toEquiv_inclusion_apply hfg (v x))
        have hx :
            ((fun z : g.1.cod ↦ (z : N)) ∘ g.1.toEquiv ∘ xs') =
              ((fun z : f.1.cod ↦ (z : N)) ∘ f.1.toEquiv ∘ xs) := by
          funext i
          exact congrArg Subtype.val (PartialEquiv.toEquiv_inclusion_apply hfg (xs i))
        have hb : (g.1.toEquiv b : N) = a := by
          exact congrArg Subtype.val (g.1.toEquiv.apply_symm_apply ⟨a, ha⟩)
        rw [hv] at hright
        have htuple :
            ((fun z : g.1.cod ↦ (z : N)) ∘
                Fin.snoc (g.1.toEquiv ∘ xs') (g.1.toEquiv b)) =
              Fin.snoc ((fun z : f.1.cod ↦ (z : N)) ∘ f.1.toEquiv ∘ xs) a := by
          rw [Fin.comp_snoc]
          exact congrArg₂ Fin.snoc hx hb
        rw [htuple] at hright
        exact hright
      · intro h (a : M)
        obtain ⟨g, ha, hfg⟩ := hMN f a
        let v' : _ → g.1.dom :=
          Substructure.inclusion (PartialEquiv.dom_le_dom hfg) ∘ v
        let xs' : Fin k → g.1.dom :=
          Substructure.inclusion (PartialEquiv.dom_le_dom hfg) ∘ xs
        let a' : g.1.dom := ⟨a, ha⟩
        let b : g.1.cod := g.1.toEquiv a'
        have hv :
            ((fun z : g.1.cod ↦ (z : N)) ∘ g.1.toEquiv ∘ v') =
              ((fun z : f.1.cod ↦ (z : N)) ∘ f.1.toEquiv ∘ v) := by
          funext x
          exact congrArg Subtype.val (PartialEquiv.toEquiv_inclusion_apply hfg (v x))
        have hx :
            ((fun z : g.1.cod ↦ (z : N)) ∘ g.1.toEquiv ∘ xs') =
              ((fun z : f.1.cod ↦ (z : N)) ∘ f.1.toEquiv ∘ xs) := by
          funext i
          exact congrArg Subtype.val (PartialEquiv.toEquiv_inclusion_apply hfg (xs i))
        have hright :
            θ.Realize ((fun z : g.1.cod ↦ (z : N)) ∘ g.1.toEquiv ∘ v')
              ((fun z : g.1.cod ↦ (z : N)) ∘ g.1.toEquiv ∘ Fin.snoc xs' a') := by
          rw [Fin.comp_snoc, hv]
          have htuple :
              ((fun z : g.1.cod ↦ (z : N)) ∘
                  Fin.snoc (g.1.toEquiv ∘ xs') (g.1.toEquiv a')) =
                Fin.snoc ((fun z : f.1.cod ↦ (z : N)) ∘ f.1.toEquiv ∘ xs) (b : N) := by
            rw [Fin.comp_snoc]
            exact congrArg₂ Fin.snoc hx rfl
          rw [htuple]
          exact h (b : N)
        have hleft := (ih g v' (Fin.snoc xs' a')).mpr hright
        rw [Fin.comp_snoc] at hleft
        simpa [v', xs', a', Function.comp_def] using hleft

private theorem isQF_foldr_inf {α : Type*} {n : ℕ}
    (l : List (Language.order.BoundedFormula α n))
    (hl : ∀ φ ∈ l, φ.IsQF) : (l.foldr (· ⊓ ·) ⊤).IsQF := by
  induction l with
  | nil => exact BoundedFormula.IsQF.top
  | cons φ l ih =>
      exact (hl φ (by simp)).inf (ih fun ψ hψ ↦ hl ψ (by simp [hψ]))

private theorem isQF_foldr_sup {α : Type*} {n : ℕ}
    (l : List (Language.order.BoundedFormula α n))
    (hl : ∀ φ ∈ l, φ.IsQF) : (l.foldr (· ⊔ ·) ⊥).IsQF := by
  induction l with
  | nil => exact BoundedFormula.isQF_bot
  | cons φ l ih =>
      exact (hl φ (by simp)).sup (ih fun ψ hψ ↦ hl ψ (by simp [hψ]))

private def orderAtom {α : Type*} {n : ℕ}
    (r : (α ⊕ Fin n) → (α ⊕ Fin n) → Bool)
    (p : (α ⊕ Fin n) × (α ⊕ Fin n)) : Language.order.BoundedFormula α n :=
  if r p.1 p.2 then
    (Language.leSymb : Language.order.Relations 2).boundedFormula₂
      (Language.Term.var p.1) (Language.Term.var p.2)
  else
    ∼((Language.leSymb : Language.order.Relations 2).boundedFormula₂
      (Language.Term.var p.1) (Language.Term.var p.2))

private noncomputable def orderDiagram {α : Type*} [Finite α] {n : ℕ}
    (r : (α ⊕ Fin n) → (α ⊕ Fin n) → Bool) : Language.order.BoundedFormula α n := by
  classical
  let _ := Fintype.ofFinite α
  exact ((Finset.univ : Finset ((α ⊕ Fin n) × (α ⊕ Fin n))).toList.map
    (orderAtom r)).foldr (· ⊓ ·) ⊤

private theorem orderAtom_isQF {α : Type*}
    (r : (α ⊕ Fin n) → (α ⊕ Fin n) → Bool)
    (p : (α ⊕ Fin n) × (α ⊕ Fin n)) : (orderAtom r p).IsQF := by
  classical
  simp only [orderAtom]
  split
  · exact Language.Relations.isQF _ _
  · exact (Language.Relations.isQF _ _).not

private theorem orderDiagram_isQF {α : Type*} [Finite α]
    (r : (α ⊕ Fin n) → (α ⊕ Fin n) → Bool) : (orderDiagram r).IsQF := by
  classical
  let _ := Fintype.ofFinite α
  apply isQF_foldr_inf
  intro ψ hψ
  simp only [List.mem_map, Finset.mem_toList] at hψ
  obtain ⟨p, _, rfl⟩ := hψ
  exact orderAtom_isQF r p

private theorem realize_orderAtom {α : Type*}
    (r : (α ⊕ Fin n) → (α ⊕ Fin n) → Bool)
    (p : (α ⊕ Fin n) × (α ⊕ Fin n))
    {M : Type*} [Language.order.Structure M] [LE M]
    [Language.order.OrderedStructure M]
    (v : α → M) (xs : Fin n → M) :
    (orderAtom r p).Realize v xs ↔
      (r p.1 p.2 = true ↔ Sum.elim v xs p.1 ≤ Sum.elim v xs p.2) := by
  classical
  by_cases hr : r p.1 p.2 = true
  · simp [orderAtom, hr]
  · have hr' : r p.1 p.2 = false := Bool.eq_false_of_not_eq_true hr
    simp [orderAtom, hr']

private theorem realize_orderDiagram {α : Type*} [Finite α]
    (r : (α ⊕ Fin n) → (α ⊕ Fin n) → Bool)
    {M : Type*} [Language.order.Structure M] [LE M]
    [Language.order.OrderedStructure M]
    (v : α → M) (xs : Fin n → M) :
    (orderDiagram r).Realize v xs ↔
      ∀ a b, (r a b = true ↔ Sum.elim v xs a ≤ Sum.elim v xs b) := by
  classical
  let _ := Fintype.ofFinite α
  rw [orderDiagram, BoundedFormula.realize_foldr_inf]
  constructor
  · intro h a b
    exact (realize_orderAtom r (a, b) v xs).mp (h _ (by simp))
  · intro h ψ hψ
    simp only [List.mem_map, Finset.mem_toList] at hψ
    obtain ⟨p, _, rfl⟩ := hψ
    exact (realize_orderAtom r p v xs).mpr (h p.1 p.2)

private noncomputable def qfForFinite {α : Type*} [Finite α] {n : ℕ}
    (φ : Language.order.BoundedFormula α n) : Language.order.BoundedFormula α n := by
  classical
  let _ := Fintype.ofFinite α
  let Profiles := (α ⊕ Fin n) → (α ⊕ Fin n) → Bool
  let Good : Profiles → Prop := fun r ↦
    ∃ (v : α → ℚ) (xs : Fin n → ℚ),
      @BoundedFormula.Realize Language.order ℚ (Language.orderStructure ℚ) α n φ v xs ∧
      ∀ a b, (r a b = true ↔ Sum.elim v xs a ≤ Sum.elim v xs b)
  exact ((Finset.univ : Finset Profiles).toList.filter Good).map
    (fun r ↦ orderDiagram r) |>.foldr (· ⊔ ·) ⊥

private theorem qfForFinite_isQF {α : Type*} [Finite α] {n : ℕ}
    (φ : Language.order.BoundedFormula α n) : (qfForFinite φ).IsQF := by
  classical
  let _ := Fintype.ofFinite α
  unfold qfForFinite
  apply isQF_foldr_sup
  intro ψ hψ
  simp only [List.mem_map, List.mem_filter] at hψ
  obtain ⟨r, _, rfl⟩ := hψ
  exact orderDiagram_isQF r

private theorem eq_iff_eq_of_same_orderProfile
    {β M N : Type*} [PartialOrder M] [PartialOrder N]
    (x : β → M) (y : β → N)
    (h : ∀ i j, (x i ≤ x j ↔ y i ≤ y j)) (i j : β) :
    x i = x j ↔ y i = y j := by
  constructor
  · intro hij
    apply le_antisymm
    · exact (h i j).mp hij.le
    · exact (h j i).mp hij.ge
  · intro hij
    apply le_antisymm
    · exact (h i j).mpr hij.le
    · exact (h j i).mpr hij.ge

private noncomputable def rangeOrderIso
    {β M N : Type*} [PartialOrder M] [PartialOrder N]
    (x : β → M) (y : β → N)
    (h : ∀ i j, (x i ≤ x j ↔ y i ≤ y j)) : Set.range x ≃o Set.range y := by
  classical
  let g : Set.range x → Set.range y := fun a =>
    ⟨y (Classical.choose a.property), ⟨Classical.choose a.property, rfl⟩⟩
  have hg_le (a b : Set.range x) : g a ≤ g b ↔ a ≤ b := by
    let i := Classical.choose a.property
    let j := Classical.choose b.property
    have hi : x i = a := Classical.choose_spec a.property
    have hj : x j = b := Classical.choose_spec b.property
    change y i ≤ y j ↔ a.1 ≤ b.1
    rw [← h i j, hi, hj]
  have hg_inj : Function.Injective g := by
    intro a b hab
    apply le_antisymm
    · exact (hg_le a b).mp (le_of_eq hab)
    · exact (hg_le b a).mp (le_of_eq hab.symm)
  have hg_surj : Function.Surjective g := by
    rintro ⟨_, i, rfl⟩
    let a : Set.range x := ⟨x i, ⟨i, rfl⟩⟩
    refine ⟨a, Subtype.ext ?_⟩
    change y (Classical.choose a.property) = y i
    exact (eq_iff_eq_of_same_orderProfile x y h _ _).mp
      (Classical.choose_spec a.property)
  refine ⟨Equiv.ofBijective g ⟨hg_inj, hg_surj⟩, ?_⟩
  intro a b
  exact hg_le a b

private theorem rangeOrderIso_apply
    {β M N : Type*} [PartialOrder M] [PartialOrder N]
    (x : β → M) (y : β → N)
    (h : ∀ i j, (x i ≤ x j ↔ y i ≤ y j)) (i : β) :
    (rangeOrderIso x y h ⟨x i, ⟨i, rfl⟩⟩ : N) = y i := by
  classical
  unfold rangeOrderIso
  dsimp only [Equiv.ofBijective_apply]
  exact (eq_iff_eq_of_same_orderProfile x y h _ _).mp
    (Classical.choose_spec (show x i ∈ Set.range x from ⟨i, rfl⟩))

private noncomputable def fgequivOfSameOrderProfile
    {β M N : Type*} [Finite β]
    [Language.order.Structure M] [Language.order.Structure N]
    [LinearOrder M] [LinearOrder N]
    [Language.order.OrderedStructure M] [Language.order.OrderedStructure N]
    (x : β → M) (y : β → N)
    (h : ∀ i j, (x i ≤ x j ↔ y i ≤ y j)) : Language.order.FGEquiv M N := by
  classical
  let S : Language.order.Substructure M := Substructure.closure Language.order (Set.range x)
  let T : Language.order.Substructure N := Substructure.closure Language.order (Set.range y)
  let eRange : Set.range x ≃o Set.range y := rangeOrderIso x y h
  let eST : S ≃o T :=
    (OrderIso.setCongr (S : Set M) (Set.range x)
      (by simp [S, Substructure.closure_eq_of_isRelational])).trans <|
      eRange.trans <|
        (OrderIso.setCongr (Set.range y) (T : Set N)
          (by simp [T, Substructure.closure_eq_of_isRelational]))
  exact ⟨⟨S, T, StrongHomClass.toEquiv eST⟩, Substructure.fg_closure (Set.finite_range x)⟩

private theorem fgequivOfSameOrderProfile_apply
    {β M N : Type*} [Finite β]
    [Language.order.Structure M] [Language.order.Structure N]
    [LinearOrder M] [LinearOrder N]
    [Language.order.OrderedStructure M] [Language.order.OrderedStructure N]
    (x : β → M) (y : β → N)
    (h : ∀ i j, (x i ≤ x j ↔ y i ≤ y j)) (i : β) :
    (((fgequivOfSameOrderProfile x y h).1.toEquiv
      ⟨x i, by simp [fgequivOfSameOrderProfile,
        Substructure.mem_closure_iff_of_isRelational]⟩ : _) : N) = y i := by
  classical
  unfold fgequivOfSameOrderProfile
  change ((rangeOrderIso x y h ⟨x i, ⟨i, rfl⟩⟩ : Set.range y) : N) = y i
  exact rangeOrderIso_apply x y h i

private theorem realize_qfForFinite {α : Type*} [Finite α] {n : ℕ}
    (φ : Language.order.BoundedFormula α n)
    (M : Type*) [Language.order.Structure M]
    [M ⊨ Language.order.dlo ∪ Language.order.nonemptyTheory]
    (v : α → M) (xs : Fin n → M) :
    φ.Realize v xs ↔ (qfForFinite φ).Realize v xs := by
  classical
  let _ := Fintype.ofFinite α
  have hne : Nonempty M := (Language.model_nonemptyTheory_iff Language.order).mp
    (show M ⊨ Language.order.nonemptyTheory from
      ‹M ⊨ Language.order.dlo ∪ Language.order.nonemptyTheory›.mono Set.subset_union_right)
  letI : Nonempty M := hne
  have hdlo : M ⊨ Language.order.dlo :=
    ‹M ⊨ Language.order.dlo ∪ Language.order.nonemptyTheory›.mono Set.subset_union_left
  letI : M ⊨ Language.order.dlo := hdlo
  letI : LinearOrder M := Language.order.linearOrderOfModels M
  letI : Language.order.OrderedStructure M := inferInstance
  letI : Language.order.Structure ℚ := Language.orderStructure ℚ
  letI : Language.order.OrderedStructure ℚ := ⟨fun _ ↦ Iff.rfl⟩
  letI : ℚ ⊨ Language.order.dlo := inferInstance
  let r : (α ⊕ Fin n) → (α ⊕ Fin n) → Bool :=
    fun a b ↦ decide (Sum.elim v xs a ≤ Sum.elim v xs b)
  have hr (a b : α ⊕ Fin n) :
      r a b = true ↔ Sum.elim v xs a ≤ Sum.elim v xs b := by
    simp [r]
  constructor
  · intro hφ
    let X : Set M := Set.range v ∪ Set.range xs
    have hXfin : X.Finite := (Set.finite_range v).union (Set.finite_range xs)
    letI : Fintype X := hXfin.fintype
    let eXQ : X ↪o ℚ := Classical.choice (nonempty_orderEmbedding_of_finite_infinite X ℚ)
    let vQ : α → ℚ := fun a ↦ eXQ ⟨v a, Set.mem_union_left _ ⟨a, rfl⟩⟩
    let xsQ : Fin n → ℚ := fun i ↦ eXQ ⟨xs i, Set.mem_union_right _ ⟨i, rfl⟩⟩
    have hprof (i j : α ⊕ Fin n) :
        (Sum.elim vQ xsQ i ≤ Sum.elim vQ xsQ j ↔
          Sum.elim v xs i ≤ Sum.elim v xs j) := by
      rcases i with i | i <;> rcases j with j | j <;>
        simp only [Sum.elim_inl, Sum.elim_inr, vQ, xsQ, OrderEmbedding.le_iff_le] <;>
        rfl
    let f := fgequivOfSameOrderProfile
      (M := ℚ) (N := M) (Sum.elim vQ xsQ) (Sum.elim v xs) hprof
    let vDom : α → f.1.dom := fun a ↦
      ⟨vQ a, by
        simp only [f, fgequivOfSameOrderProfile,
          Substructure.mem_closure_iff_of_isRelational]
        exact ⟨Sum.inl a, rfl⟩⟩
    let xsDom : Fin n → f.1.dom := fun i ↦
      ⟨xsQ i, by
        simp only [f, fgequivOfSameOrderProfile,
          Substructure.mem_closure_iff_of_isRelational]
        exact ⟨Sum.inr i, rfl⟩⟩
    have hmapv (a : α) : ((f.1.toEquiv (vDom a) : _) : M) = v a := by
      simpa [f, vDom] using fgequivOfSameOrderProfile_apply
        (M := ℚ) (N := M) (Sum.elim vQ xsQ) (Sum.elim v xs) hprof (Sum.inl a)
    have hmapxs (i : Fin n) : ((f.1.toEquiv (xsDom i) : _) : M) = xs i := by
      simpa [f, xsDom] using fgequivOfSameOrderProfile_apply
        (M := ℚ) (N := M) (Sum.elim vQ xsQ) (Sum.elim v xs) hprof (Sum.inr i)
    have hiff := realize_iff_of_fgequiv
      (φ := φ) (f := f) (v := vDom) (xs := xsDom)
      (Language.dlo_isExtensionPair ℚ M) (Language.dlo_isExtensionPair M ℚ)
    have hright :
        φ.Realize ((fun z : f.1.cod ↦ (z : M)) ∘ f.1.toEquiv ∘ vDom)
          ((fun z : f.1.cod ↦ (z : M)) ∘ f.1.toEquiv ∘ xsDom) := by
      convert hφ using 1
      · funext a
        exact hmapv a
      · funext i
        exact hmapxs i
    have hφQ : φ.Realize vQ xsQ := by
      have hleft := hiff.mpr hright
      simpa [vDom, xsDom, Function.comp_def] using hleft
    unfold qfForFinite
    rw [BoundedFormula.realize_foldr_sup]
    refine ⟨orderDiagram r, ?_, (realize_orderDiagram r v xs).mpr hr⟩
    simp only [List.mem_map, List.mem_filter, Finset.mem_toList, Finset.mem_univ, true_and]
    refine ⟨r, ?_, rfl⟩
    have hgood : ∃ (v : α → ℚ) (xs : Fin n → ℚ),
        φ.Realize v xs ∧ ∀ a b,
          (r a b = true ↔ Sum.elim v xs a ≤ Sum.elim v xs b) := by
      refine ⟨vQ, xsQ, hφQ, ?_⟩
      intro a b
      simpa [r] using (hprof a b).symm
    simpa only [List.mem_filter, Finset.mem_toList, Finset.mem_univ, true_and,
      decide_eq_true_eq] using hgood
  · intro hqf
    unfold qfForFinite at hqf
    rw [BoundedFormula.realize_foldr_sup] at hqf
    obtain ⟨ψ, hψ, hψreal⟩ := hqf
    simp only [List.mem_map] at hψ
    obtain ⟨r', hr'mem, hψeq⟩ := hψ
    subst ψ
    have hr'good : ∃ (v : α → ℚ) (xs : Fin n → ℚ),
        φ.Realize v xs ∧ ∀ a b,
          (r' a b = true ↔ Sum.elim v xs a ≤ Sum.elim v xs b) := by
      simpa only [List.mem_filter, Finset.mem_toList, Finset.mem_univ, true_and,
        decide_eq_true_eq] using hr'mem
    obtain ⟨vQ, xsQ, hφQ, hrQ⟩ := hr'good
    have hrM := (realize_orderDiagram r' v xs).mp hψreal
    have hprof (i j : α ⊕ Fin n) :
        (Sum.elim vQ xsQ i ≤ Sum.elim vQ xsQ j ↔
          Sum.elim v xs i ≤ Sum.elim v xs j) :=
      (hrQ i j).symm.trans (hrM i j)
    let f := fgequivOfSameOrderProfile
      (M := ℚ) (N := M) (Sum.elim vQ xsQ) (Sum.elim v xs) hprof
    let vDom : α → f.1.dom := fun a ↦
      ⟨vQ a, by
        simp only [f, fgequivOfSameOrderProfile,
          Substructure.mem_closure_iff_of_isRelational]
        exact ⟨Sum.inl a, rfl⟩⟩
    let xsDom : Fin n → f.1.dom := fun i ↦
      ⟨xsQ i, by
        simp only [f, fgequivOfSameOrderProfile,
          Substructure.mem_closure_iff_of_isRelational]
        exact ⟨Sum.inr i, rfl⟩⟩
    have hmapv (a : α) : ((f.1.toEquiv (vDom a) : _) : M) = v a := by
      simpa [f, vDom] using fgequivOfSameOrderProfile_apply
        (M := ℚ) (N := M) (Sum.elim vQ xsQ) (Sum.elim v xs) hprof (Sum.inl a)
    have hmapxs (i : Fin n) : ((f.1.toEquiv (xsDom i) : _) : M) = xs i := by
      simpa [f, xsDom] using fgequivOfSameOrderProfile_apply
        (M := ℚ) (N := M) (Sum.elim vQ xsQ) (Sum.elim v xs) hprof (Sum.inr i)
    have hiff := realize_iff_of_fgequiv
      (φ := φ) (f := f) (v := vDom) (xs := xsDom)
      (Language.dlo_isExtensionPair ℚ M) (Language.dlo_isExtensionPair M ℚ)
    have hleft :
        φ.Realize ((fun z : f.1.dom ↦ (z : ℚ)) ∘ vDom)
          ((fun z : f.1.dom ↦ (z : ℚ)) ∘ xsDom) := by
      simpa [vDom, xsDom, Function.comp_def] using hφQ
    have hright := hiff.mp hleft
    convert hright using 1
    · funext a
      exact (hmapv a).symm
    · funext i
      exact (hmapxs i).symm

private theorem isQF_subst {L : Language} {α β : Type*} {n : ℕ}
    {φ : L.BoundedFormula α n} (hφ : φ.IsQF) (f : α → L.Term β) :
    (φ.subst f).IsQF := by
  induction hφ with
  | falsum => exact BoundedFormula.isQF_bot
  | of_isAtomic h =>
      induction h with
      | equal t₁ t₂ => exact (BoundedFormula.IsAtomic.equal _ _).isQF
      | rel R ts => exact (BoundedFormula.IsAtomic.rel R _).isQF
  | imp _ _ ih₁ ih₂ => exact ih₁.imp ih₂

/-- **Quantifier Elimination for Dense Linear Orders**:
The theory of dense linear orders without endpoints (DLO)
admits quantifier elimination. -/
theorem MainTheorem :
    EliminatesQuantifiers (Language.order.dlo ∪ Language.order.nonemptyTheory) := by
  classical
  intro α n φ
  let β := φ.freeVarFinset
  let φ' : Language.order.BoundedFormula β n := φ.restrictFreeVar id
  let ψ' := qfForFinite φ'
  let ψ : Language.order.BoundedFormula α n :=
    ψ'.subst fun a ↦ Language.Term.var a.1
  refine ⟨ψ, ?_, ?_⟩
  · exact isQF_subst (qfForFinite_isQF φ') _
  · intro M _ _ v xs
    let v' : β → M := v ∘ Subtype.val
    have hrestrict : φ'.Realize v' xs ↔ φ.Realize v xs := by
      exact BoundedFormula.realize_restrictFreeVar v (by simp [v'])
    have hfinite := realize_qfForFinite φ' M v' xs
    have hsubst : ψ.Realize v xs ↔ ψ'.Realize v' xs := by
      rw [show ψ = ψ'.subst (fun a ↦ Language.Term.var a.1) from rfl,
        BoundedFormula.realize_subst]
      change ψ'.Realize (fun a : β ↦ v a.1) xs ↔ ψ'.Realize v' xs
      rfl
    exact hrestrict.symm.trans (hfinite.trans hsubst.symm)

end DLOQuantifierElimination
