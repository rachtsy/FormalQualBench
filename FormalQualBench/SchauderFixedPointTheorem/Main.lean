import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Set.Operations

namespace SchauderFixedPointTheorem

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Schauder fixed point theorem (statement)**: a continuous self-map of a nonempty compact
convex subset of a Banach space has a fixed point. -/
theorem MainTheorem {s : Set E} (hs_nonempty : s.Nonempty) (hs_compact : IsCompact s)
    (hs_convex : Convex ℝ s) {f : E → E} (hf_cont : ContinuousOn f s)
    (hf_maps : Set.MapsTo f s s) :
    ∃ x ∈ s, f x = x := by
  sorry

end SchauderFixedPointTheorem
