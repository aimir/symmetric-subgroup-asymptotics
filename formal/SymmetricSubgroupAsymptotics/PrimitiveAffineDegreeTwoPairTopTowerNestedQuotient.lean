import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopTowerQuotient
import SymmetricSubgroupAsymptotics.BinaryPairRankThreeResidual

/-!
# The inner omega layer as a nested natural-module quotient

The second-frame image of direct-kernel omega is obtained by quotienting its
natural coordinate axis by the coordinate axis of the original normal
subgroup.  This file identifies that literal quotient with the exact image
of the corresponding state in the actual pair section.  It also transports
the action from the selected catalogue top to the physical second-frame top.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairTopTowerRealization

variable {s t : ℕ} {D : DegreeTwoPairTopFiniteInterface t}
  {p : PreE7PairActionClass s}
  (R : DegreeTwoPairTopTowerRealization D p)

/-- The original-normal coordinate axis is contained in the inner omega
coordinate axis. -/
theorem moduleAxis_le_innerOmegaNaturalAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.moduleAxis N ≤ R.innerOmegaNaturalAxis N := by
  intro v hv
  change v ∈ R.secondFrame.ambientAxis
    (R.rawKernelOmegaIntermediatePreimage N)
  change v ∈ R.secondFrame.ambientAxis (R.outerTopNormal N.1) at hv
  obtain ⟨k, hk, rfl⟩ := (R.secondFrame.mem_ambientAxis _ v).1 hv
  exact (R.secondFrame.mem_ambientAxis _ _).2
    ⟨k, R.outerTopNormal_le_rawKernelOmegaIntermediatePreimage N hk, rfl⟩

/-- Pulling the literal nested quotient back along the top equivalence gives
the identical quotient formed in physical second-frame coordinates. -/
def innerNestedQuotientCoordinateEquiv
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    ((nestedQuotientRepresentation
      (R.moduleAxis N) (R.innerOmegaNaturalAxis N)
      (R.moduleAxis_le_innerOmegaNaturalAxis N)).comp
        R.topEquiv.symm.toMonoidHom).Equiv
      (nestedQuotientRepresentation
        (R.innerNormalCoordinateAxis N) (R.innerOmegaCoordinateAxis N)
        (R.innerNormalCoordinateAxis_le_innerOmegaCoordinateAxis N)) :=
  Representation.Equiv.mk (LinearEquiv.refl _ _) (by
    intro g
    apply LinearMap.ext
    intro x
    obtain ⟨b, rfl⟩ :=
      (nestedSubrepresentation
        (R.moduleAxis N) (R.innerOmegaNaturalAxis N)
        (R.moduleAxis_le_innerOmegaNaturalAxis N)).toSubmodule.
          mkQ_surjective x
    apply congrArg
      (nestedSubrepresentation
        (R.innerNormalCoordinateAxis N) (R.innerOmegaCoordinateAxis N)
        (R.innerNormalCoordinateAxis_le_innerOmegaCoordinateAxis N)).toSubmodule.mkQ
    apply Subtype.ext
    rw [R.module_action_eq, R.topEquiv.apply_symm_apply])

/-- The transported natural quotient is the exact image of the omega state
under the actual second-frame section map. -/
noncomputable def innerNestedQuotientSectionImageEquiv
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    ((nestedQuotientRepresentation
      (R.moduleAxis N) (R.innerOmegaNaturalAxis N)
      (R.moduleAxis_le_innerOmegaNaturalAxis N)).comp
        R.topEquiv.symm.toMonoidHom).Equiv
      (intertwinerImage
        R.secondFrame.kernelTopPermutationSubrepresentation.toRepresentation
        (R.secondFrame.sectionTopRepresentation (R.outerTopNormal N.1))
        (R.secondFrame.sectionTopIntertwiner (R.outerTopNormal N.1))
        (nestedSubrepresentation (R.innerOmegaCoordinateAxis N)
          R.secondFrame.kernelTopPermutationSubrepresentation
          (R.innerOmegaCoordinateAxis_le_kernelTop N))).toRepresentation := by
  let hAB : R.secondFrame.normalTopPermutationSubrepresentation
      (R.outerTopNormal N.1) ≤ R.innerOmegaCoordinateAxis N := by
    rw [← R.innerNormalCoordinateAxis_eq_normalTopPermutation N]
    exact R.innerNormalCoordinateAxis_le_innerOmegaCoordinateAxis N
  let eImage := R.secondFrame.sectionTopNestedQuotientImageEquiv
    (R.outerTopNormal N.1) (R.innerOmegaCoordinateAxis N) hAB
      (R.innerOmegaCoordinateAxis_le_kernelTop N)
  rw [← R.innerNormalCoordinateAxis_eq_normalTopPermutation N] at eImage
  exact (R.innerNestedQuotientCoordinateEquiv N).trans eImage

end DegreeTwoPairTopTowerRealization
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
