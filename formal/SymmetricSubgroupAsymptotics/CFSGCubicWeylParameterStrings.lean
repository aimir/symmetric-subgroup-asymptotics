import SymmetricSubgroupAsymptotics.CFSGQuadraticWeylParameterStrings

/-! The parameterized rank-one Weyl word on a four-term divided-power
string. Only the nonzero torus parameter is inverted; 2 and 3 are never
inverted. This is the length-four calculation needed at a G2 triple edge. -/
set_option autoImplicit false
set_option Elab.async false

namespace SymmetricSubgroupAsymptotics.CFSGCubicWeylParameterStrings
open CFSGQuadraticWeylParameterStrings
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

theorem word_quadruple (U V : K → Module.End K M) (t : Kˣ) (x₀ x₁ x₂ x₃ : M)
    (hU₀ : ∀ a, U a x₀ = x₀ + a • x₁ + a ^ 2 • x₂ + a ^ 3 • x₃)
    (hU₁ : ∀ a, U a x₁ = x₁ + (2 * a) • x₂ + (3 * a ^ 2) • x₃)
    (hU₂ : ∀ a, U a x₂ = x₂ + (3 * a) • x₃)
    (hU₃ : ∀ a, U a x₃ = x₃)
    (hV₀ : ∀ a, V a x₀ = x₀)
    (hV₁ : ∀ a, V a x₁ = x₁ + (3 * a) • x₀)
    (hV₂ : ∀ a, V a x₂ = x₂ + (2 * a) • x₁ + (3 * a ^ 2) • x₀)
    (hV₃ : ∀ a, V a x₃ = x₃ + a • x₂ + a ^ 2 • x₁ + a ^ 3 • x₀) :
    word U V t x₀ = (t : K) ^ 3 • x₃ ∧
      word U V t x₁ = -(t : K) • x₂ ∧
      word U V t x₂ = (t : K)⁻¹ • x₁ ∧
      word U V t x₃ = -((t : K)⁻¹) ^ 3 • x₀ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [word, Module.End.mul_apply, hU₀, hU₁, hU₂, hU₃,
      hV₀, hV₁, hV₂, hV₃, map_add, map_smul] <;>
    match_scalars <;> field_simp [Units.ne_zero t] <;> ring

end SymmetricSubgroupAsymptotics.CFSGCubicWeylParameterStrings
