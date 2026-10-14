import SymmetricSubgroupAsymptotics.CoprimeKernelQuotientSocles
import SymmetricSubgroupAsymptotics.LinearSemidirectCoprimeSocleBounds

/-! A coprime complement's uniform normal-generator bound combines by
maximum with the actual elementary module's generator bound. This applies
to arbitrary coprime complements, including nonabelian ones. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace ElementaryCoprimeQuotientSocles

variable {G : Type} [Group G] [Finite G]
  (E : Subgroup G) [E.Normal] (C : ElementaryMinimalNormalChart E)

theorem socle_of_surjective
    (hcop : Nat.Coprime C.p (Nat.card (G ⧸ E))) (t a : ℕ)
    (hgen : RepresentationGeneratedBy C.quotientRepresentation.ρ t)
    (hquotient : ∀ K : Subgroup (G ⧸ E), K.Normal → MarkedC4.normalGen K ≤ a)
    {Q : Type} [Group Q] (pi : G →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q (max t a) := by
  apply CoprimeKernelQuotientSocles.socle_of_surjective C.p E
    (CoprimeCyclicElementarySocles.kernel_isPGroup E C) hcop t a ?_ hquotient pi hpi
  intro H hH hHE
  letI := hH
  exact CoprimeCyclicElementarySocleBounds.kernel_normalGen_le E C hcop t hgen H hHE

end ElementaryCoprimeQuotientSocles

namespace LinearSemidirectCoprimeQuotientSocles

open LinearSemidirectCoprimeSocleBounds

variable {p : ℕ} [Fact p.Prime]
  {R V : Type} [Group R] [Finite R] [AddCommGroup V] [Module (ZMod p) V]
  [FiniteDimensional (ZMod p) V]
  (rho : R →* (V ≃ₗ[ZMod p] V))

theorem socle_of_surjective
    (hcop : Nat.Coprime p (Nat.card R)) (t a : ℕ)
    (hgen : RepresentationGeneratedBy (linearRepresentation rho) t)
    (hR : ∀ K : Subgroup R, K.Normal → MarkedC4.normalGen K ≤ a)
    {Q : Type} [Group Q] (pi : Model rho →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q (max t a) := by
  have hcopQuotient : Nat.Coprime p (Nat.card (Model rho ⧸ translationKernel rho)) := by
    rw [Nat.card_congr (complementEquiv rho).toEquiv]
    exact hcop
  apply ElementaryCoprimeQuotientSocles.socle_of_surjective
    (translationKernel rho) (translationChart rho) hcopQuotient t a
    (translationRepresentation_generated rho hgen) ?_ pi hpi
  intro K hK
  letI := hK
  exact CoprimeKernelQuotientSocles.normalGen_image_bound
    (complementEquiv rho).symm.toMonoidHom (complementEquiv rho).symm.surjective a hR K

theorem quotient
    (hcop : Nat.Coprime p (Nat.card R)) (t a : ℕ)
    (hgen : RepresentationGeneratedBy (linearRepresentation rho) t)
    (hR : ∀ K : Subgroup R, K.Normal → MarkedC4.normalGen K ≤ a)
    (N : Subgroup (Model rho)) [N.Normal] :
    SocleNormalGeneratorBound (Model rho ⧸ N) (max t a) :=
  socle_of_surjective rho hcop t a hgen hR
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end LinearSemidirectCoprimeQuotientSocles
end SymmetricSubgroupAsymptotics

end
