import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
import Mathlib.Analysis.VonNeumannAlgebra.Basic

namespace VonNeumannDoubleCommutantTheorem

open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **von Neumann double commutant theorem (statement)**:
for a unital *-subalgebra `S ⊆ B(H)`, being closed in the weak operator topology is equivalent to
being equal to its bicommutant. -/
theorem MainTheorem (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    IsClosed ((ContinuousLinearMap.toWOT (RingHom.id ℂ) H H) '' (S : Set (H →L[ℂ] H))) ↔
      Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) = (S : Set (H →L[ℂ] H)) := by
  sorry

end VonNeumannDoubleCommutantTheorem

