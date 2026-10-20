import SymmetricSubgroupAsymptotics.LinearSemidirectCoprimeQuotientSocles

/-! Uniform generators for the actual elementary kernel module give a
normal-generator bound across an arbitrary semidirect product, including
the modular case. This uses no invertibility assumption on the quotient. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace ElementaryUniformNormalGenerators

variable {G : Type} [Group G] [Finite G]
  (E : Subgroup G) [E.Normal] (C : ElementaryMinimalNormalChart E)

theorem kernel_normalGen_le (t : ℕ)
    (huniform : UniformSubrepresentationGeneratorBound C.quotientRepresentation.ρ t)
    (H : Subgroup G) [H.Normal] (hHE : H ≤ E) : MarkedC4.normalGen H ≤ t :=
  normalGen_le_of_elementaryNormalSubrepresentation_generated E C H hHE t
    (huniform (C.originalKernelChart.normalSubrepresentation
      (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)
      C.quotientRepresentation H))

theorem normalGen_le (t a : ℕ)
    (huniform : UniformSubrepresentationGeneratorBound C.quotientRepresentation.ρ t)
    (hquotient : ∀ K : Subgroup (G ⧸ E), K.Normal → MarkedC4.normalGen K ≤ a)
    (H : Subgroup G) [H.Normal] : MarkedC4.normalGen H ≤ t + a := by
  letI : (H.map (QuotientGroup.mk' E)).Normal :=
    (inferInstance : H.Normal).map _ (QuotientGroup.mk'_surjective E)
  exact (MarkedC4.normalGen_normal_le_inter_add_image H E).trans
    (Nat.add_le_add (kernel_normalGen_le E C t huniform (H ⊓ E) inf_le_right)
      (hquotient _ inferInstance))

end ElementaryUniformNormalGenerators

namespace LinearSemidirectUniformNormalGenerators

open LinearSemidirectCoprimeSocleBounds

variable {p : ℕ} [Fact p.Prime]
  {R V : Type} [Group R] [Finite R] [AddCommGroup V] [Module (ZMod p) V]
  [FiniteDimensional (ZMod p) V]
  (rho : R →* (V ≃ₗ[ZMod p] V))

theorem translationRepresentation_uniform {t : ℕ}
    (huniform : UniformSubrepresentationGeneratorBound (linearRepresentation rho) t) :
    UniformSubrepresentationGeneratorBound (translationChart rho).quotientRepresentation.ρ t := by
  apply UniformSubrepresentationGeneratorBound.of_comp
    (translationChart rho).quotientRepresentation.ρ
    (QuotientGroup.mk' (translationKernel rho))
  rw [translationRepresentation_comp]
  exact UniformSubrepresentationGeneratorBound.comp_of_surjective
    (linearRepresentation rho) (SemidirectProduct.rightHom : Model rho →* R)
    SemidirectProduct.rightHom_surjective huniform

theorem normalGen_le (t a : ℕ)
    (huniform : UniformSubrepresentationGeneratorBound (linearRepresentation rho) t)
    (hR : ∀ K : Subgroup R, K.Normal → MarkedC4.normalGen K ≤ a)
    (H : Subgroup (Model rho)) [H.Normal] : MarkedC4.normalGen H ≤ t + a := by
  apply ElementaryUniformNormalGenerators.normalGen_le
    (translationKernel rho) (translationChart rho) t a
    (translationRepresentation_uniform rho huniform) ?_ H
  intro K hK
  letI := hK
  exact CoprimeKernelQuotientSocles.normalGen_image_bound
    (complementEquiv rho).symm.toMonoidHom (complementEquiv rho).symm.surjective a hR K

end LinearSemidirectUniformNormalGenerators
end SymmetricSubgroupAsymptotics

end
