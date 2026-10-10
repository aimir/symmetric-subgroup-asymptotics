import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopTowerQuotient
import SymmetricSubgroupAsymptotics.BinaryPairRankThreeResidual

/-!
# The retained outer omega layer as a nested coordinate quotient

The part of direct-kernel omega retained in the first pair kernel is the
image, in the actual first pair section, of its literal coordinate axis.
Its denominator is exactly the coordinate axis contributed by the original
normal subgroup.  This is the outer analogue of the second-frame nested
quotient presentation.
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

/-- The original-normal coordinate axis is contained in the retained outer
omega coordinate axis. -/
theorem outerNormalAxis_le_outerOmegaAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.frame.normalTopPermutationSubrepresentation N.1 ≤
      R.outerOmegaAxis N := by
  intro v hv
  change v ∈ R.frame.ambientAxis (R.rawKernelOmegaOriginalPreimage N)
  change v ∈
    (R.frame.normalSpace N.1).map R.frame.kernelSpace.subtype at hv
  rw [R.frame.normalSpace_map_subtype_eq_ambientAxis N.1] at hv
  obtain ⟨k, hk, rfl⟩ := (R.frame.mem_ambientAxis N.1 v).1 hv
  exact (R.frame.mem_ambientAxis _ _).2
    ⟨k, R.originalNormal_le_rawKernelOmegaOriginalPreimage N hk, rfl⟩

/-- The retained outer omega coordinate axis lies in the correlated first
pair kernel state. -/
theorem outerOmegaAxis_le_kernelTop
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.outerOmegaAxis N ≤ R.frame.kernelTopPermutationSubrepresentation :=
  R.frame.ambientAxis_le_kernelSpace
    (R.rawKernelOmegaOriginalPreimage N)

/-- The literal outer quotient `B/A` is the exact image of the retained
coordinate state in the actual first-frame section. -/
noncomputable def outerNestedQuotientSectionImageEquiv
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (nestedQuotientRepresentation
      (R.frame.normalTopPermutationSubrepresentation N.1)
      (R.outerOmegaAxis N)
      (R.outerNormalAxis_le_outerOmegaAxis N)).Equiv
      (intertwinerImage
        R.frame.kernelTopPermutationSubrepresentation.toRepresentation
        (R.frame.sectionTopRepresentation N.1)
        (R.frame.sectionTopIntertwiner N.1)
        (nestedSubrepresentation (R.outerOmegaAxis N)
          R.frame.kernelTopPermutationSubrepresentation
          (R.outerOmegaAxis_le_kernelTop N))).toRepresentation :=
  R.frame.sectionTopNestedQuotientImageEquiv N.1
    (R.outerOmegaAxis N)
    (R.outerNormalAxis_le_outerOmegaAxis N)
    (R.outerOmegaAxis_le_kernelTop N)

end DegreeTwoPairTopTowerRealization
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
