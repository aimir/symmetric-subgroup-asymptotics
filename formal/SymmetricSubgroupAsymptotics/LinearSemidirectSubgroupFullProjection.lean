import SymmetricSubgroupAsymptotics.LinearSemidirectSubgroupSocles

/-! Convenience form for an arbitrary affine subgroup whose actual
projection is onto the displayed complement. Surjectivity does not
assert that the subgroup contains a pure complement. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.LinearSemidirectSubgroupFullProjection

open LinearSemidirectCoprimeSocleBounds LinearSemidirectSubgroupKernelChart

variable {p : ℕ} [Fact p.Prime]
  {R V : Type} [Group R] [Finite R] [AddCommGroup V] [Module (ZMod p) V]
  [FiniteDimensional (ZMod p) V]
  (rho : R →* (V ≃ₗ[ZMod p] V)) (K : Subgroup (Model rho))
  (hsurj : Function.Surjective (projection rho K))

def imageEquiv : Image rho K ≃* R :=
  MulEquiv.ofBijective (projection rho K).range.subtype
    ⟨Subtype.coe_injective, fun r => by
      obtain ⟨g,hg⟩ := hsurj r
      exact ⟨⟨r,⟨g,hg⟩⟩,rfl⟩⟩

include hsurj in
theorem normalGen_le (t a : ℕ)
    (huniform : UniformSubrepresentationGeneratorBound (linearRepresentation rho) t)
    (hR : ∀ L : Subgroup R, L.Normal → MarkedC4.normalGen L ≤ a)
    (N : Subgroup K) [N.Normal] : MarkedC4.normalGen N ≤ t+a := by
  apply LinearSemidirectSubgroupSocles.normalGen_le rho K t a ?_ ?_ N
  · exact UniformSubrepresentationGeneratorBound.comp_of_surjective
      (linearRepresentation rho) (projection rho K).range.subtype
      (imageEquiv rho K hsurj).surjective huniform
  · intro L hL
    letI := hL
    exact CoprimeKernelQuotientSocles.normalGen_image_bound
      (imageEquiv rho K hsurj).symm.toMonoidHom
      (imageEquiv rho K hsurj).symm.surjective a hR L

end SymmetricSubgroupAsymptotics.LinearSemidirectSubgroupFullProjection

end
