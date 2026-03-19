import Mathlib.Analysis.Complex.CauchyIntegral

namespace RungeTheorem

open scoped Topology

/-- **Runge's theorem (statement)**: a holomorphic function on an open set can be approximated
uniformly on a compact subset (with connected complement) by polynomials. -/
theorem MainTheorem {U K : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hKc : IsConnected (Kᶜ)) (hf : DifferentiableOn ℂ f U) :
    ∀ ε > 0, ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖p.eval z - f z‖ < ε := by
  sorry

end RungeTheorem

