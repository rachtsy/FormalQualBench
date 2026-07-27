import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Finsubgraph

namespace DeBruijnErdos

open SimpleGraph

/-- The de Bruijn-Erdős theorem: If every finite subgraph of G is k-colorable,
then G itself is k-colorable. -/
theorem MainTheorem {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    (∀ s : Finset V, (G.induce (↑s : Set V)).Colorable k) → G.Colorable k := by
  intro h
  exact
    SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom (G := G)
      (F := completeGraph (Fin k)) fun G' hG' =>
        (h hG'.toFinset).some.comp
          { toFun := fun v => ⟨v, by simp [v.2]⟩
            map_rel' := fun hvw => G'.adj_sub hvw }

end DeBruijnErdos
