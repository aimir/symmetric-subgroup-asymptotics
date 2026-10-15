import SymmetricSubgroupAsymptotics.BinarySignTernaryLinear

/-! A common signed four-block affine quotient bound. The literal binary
sign subspace and the original complement remain in the model. All quotient
maps are supplied by the caller; no subgroup containment transfers a bound. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinarySignTernaryAffineSocles

open SemidirectProduct BinarySignTernaryLinear

variable {R : Type} [Group R] [MulAction R (Fin 4)] [FaithfulSMul R (Fin 4)]
variable (E : Subrepresentation
  (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation (R := R) (X := Fin 4)))

abbrev Model := LinearSemidirectCoprimeSocleBounds.Model (linearHom E)

def complementEquiv : SignModel E ≃* (linearHom E).range :=
  MonoidHom.ofInjective (linearHom_injective E)

def affineEquiv : Model E ≃* AffineModel.Aff (linearHom E).range :=
  SemidirectProduct.congr (MulEquiv.refl (Multiplicative Vector)) (complementEquiv E) (by
    intro g
    apply MulEquiv.ext
    intro v
    rfl)

theorem socle_of_surjective [Finite R]
    (c : R) (hcycle : ∀ i : Fin 4, ∃ n : ℕ, c^n • 0 = i)
    (h01 : pair 0 1 ∈ E.toSubmodule) (h02 : pair 0 2 ∈ E.toSubmodule)
    (a : ℕ) (hR : ∀ K : Subgroup R, K.Normal → MarkedC4.normalGen K ≤ a)
    {Q : Type} [Group Q] (pi : Model E →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q (1+a) := by
  apply AffineModel.socle_of_surjective_of_irreducible_complement_quotients
    (linearHom E).range (irreducible E c hcycle h01 h02) (Pi.single 0 1)
    (by decide +kernel) (by omega) _
    (pi.comp (affineEquiv E).symm.toMonoidHom)
    (hpi.comp (affineEquiv E).symm.surjective)
  intro N hN
  letI := hN
  let q := (QuotientGroup.mk' N).comp (complementEquiv E).toMonoidHom
  have hq : Function.Surjective q :=
    (QuotientGroup.mk'_surjective N).comp (complementEquiv E).surjective
  exact CyclicSocleQuotientTools.socleBound_equiv
    (QuotientGroup.quotientKerEquivOfSurjective q hq)
    (CyclicOrbitBinarySignNormalGenerators.quotientSocle E c 0 hcycle a hR q.ker)

theorem quotientSocle [Finite R]
    (c : R) (hcycle : ∀ i : Fin 4, ∃ n : ℕ, c^n • 0 = i)
    (h01 : pair 0 1 ∈ E.toSubmodule) (h02 : pair 0 2 ∈ E.toSubmodule)
    (a : ℕ) (hR : ∀ K : Subgroup R, K.Normal → MarkedC4.normalGen K ≤ a)
    (N : Subgroup (Model E)) [N.Normal] : SocleNormalGeneratorBound (Model E ⧸ N) (1+a) :=
  socle_of_surjective E c hcycle h01 h02 a hR
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end SymmetricSubgroupAsymptotics.BinarySignTernaryAffineSocles

end
