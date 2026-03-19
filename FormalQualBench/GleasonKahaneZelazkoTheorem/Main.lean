import Mathlib

namespace GleasonKahaneZelazkoTheorem

/-- Gleason-Kahane-Zelazko theorem for complex Banach algebras: a normalized complex-linear
functional on a complex Banach algebra that does not vanish on invertible elements is an algebra
homomorphism. -/
theorem MainTheorem (A : Type*) [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] :
    ∀ φ : A →ₗ[ℂ] ℂ, φ 1 = 1 →
      (∀ a : A, IsUnit a → φ a ≠ 0) →
      ∃ ψ : A →ₐ[ℂ] ℂ, ψ.toLinearMap = φ := by
  sorry

end GleasonKahaneZelazkoTheorem
