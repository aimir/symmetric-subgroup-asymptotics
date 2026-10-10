import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopTowerQuotient
import SymmetricSubgroupAsymptotics.BinaryPairRankThreeResidual
import SymmetricSubgroupAsymptotics.RepresentationNestedQuotientExact

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

/-- Pair-sum image of the original-normal denominator.  Together with the
already named omega image, this gives the quotient at the right end of the
outer exact sequence. -/
def outerNormalPairSumPullbackAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation R.secondFrame.pulledBackCoordinateTopAction :=
  intertwinerImage
    (permutationFunctionRepresentation (ZMod 2)
      R.frame.top.range (Fin s))
    R.secondFrame.pulledBackCoordinateTopAction
    R.secondFrame.pairSumIntertwiner
    (R.frame.normalTopPermutationSubrepresentation N.1)

/-- Pair-constant preimage of the original-normal denominator.  Its quotient
inside the retained constant axis is the kernel at the left end of the outer
exact sequence. -/
def outerNormalConstantPullbackAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation R.secondFrame.pulledBackCoordinateTopAction :=
  intertwinerPreimage
    R.secondFrame.pulledBackCoordinateTopAction
    (permutationFunctionRepresentation (ZMod 2)
      R.frame.top.range (Fin s))
    R.secondFrame.pairConstantIntertwiner
    (R.frame.normalTopPermutationSubrepresentation N.1)

theorem outerNormalPairSum_le_outerOmegaPairSum
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.outerNormalPairSumPullbackAxis N ≤
      R.outerOmegaPairSumPullbackAxis N :=
  intertwinerImage_mono _ _ _ (R.outerNormalAxis_le_outerOmegaAxis N)

theorem outerNormalConstant_le_outerOmegaConstant
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.outerNormalConstantPullbackAxis N ≤
      R.outerOmegaConstantPullbackAxis N :=
  intertwinerPreimage_mono _ _ _ (R.outerNormalAxis_le_outerOmegaAxis N)

/-- Pair-sum induces the right-hand quotient map in the exact splitting of
the outer nested quotient. -/
noncomputable def outerNestedQuotientPairSumMap
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (nestedQuotientRepresentation
      (R.frame.normalTopPermutationSubrepresentation N.1)
      (R.outerOmegaAxis N)
      (R.outerNormalAxis_le_outerOmegaAxis N)).IntertwiningMap
      (nestedQuotientRepresentation
        (R.outerNormalPairSumPullbackAxis N)
        (R.outerOmegaPairSumPullbackAxis N)
        (R.outerNormalPairSum_le_outerOmegaPairSum N)) :=
  nestedQuotientMap
    (permutationFunctionRepresentation (ZMod 2)
      R.frame.top.range (Fin s))
    R.secondFrame.pulledBackCoordinateTopAction
    R.secondFrame.pairSumIntertwiner
    (R.frame.normalTopPermutationSubrepresentation N.1)
    (R.outerOmegaAxis N)
    (R.outerNormalAxis_le_outerOmegaAxis N)

theorem outerNestedQuotientPairSumMap_surjective
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Function.Surjective (R.outerNestedQuotientPairSumMap N) :=
  nestedQuotientMap_surjective _ _ _ _ _ _

/-- Exactness of pair-constant/pair-sum identifies the kernel of the outer
quotient map with the quotient of the two constant preimages. -/
noncomputable def outerNestedQuotientPairSumKernelEquiv
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (nestedQuotientRepresentation
      (R.outerNormalConstantPullbackAxis N)
      (R.outerOmegaConstantPullbackAxis N)
      (R.outerNormalConstant_le_outerOmegaConstant N)).Equiv
      (R.outerNestedQuotientPairSumMap N).ker.toRepresentation :=
  nestedQuotientMapKernelEquiv
    R.secondFrame.pulledBackCoordinateTopAction
    (permutationFunctionRepresentation (ZMod 2)
      R.frame.top.range (Fin s))
    R.secondFrame.pulledBackCoordinateTopAction
    R.secondFrame.pairConstantIntertwiner
    R.secondFrame.pairSumIntertwiner
    R.secondFrame.pairConstantIntertwiner_injective
    R.secondFrame.pairConstant_pairSum_exact_linear
    (R.frame.normalTopPermutationSubrepresentation N.1)
    (R.outerOmegaAxis N)
    (R.outerNormalAxis_le_outerOmegaAxis N)

/-- Descend a pair-coordinate axis from the first top to the selected
literal degree-eight top. -/
def transportOuterPullbackAxis
    (M : Subrepresentation R.secondFrame.pulledBackCoordinateTopAction) :
    Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)) :=
  R.transportInnerNaturalAxis
    (R.secondFrame.descendPulledBackSubrepresentation M)

/-- Literal denominator below the pair-sum omega state. -/
def outerNormalPairSumAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)) :=
  R.transportOuterPullbackAxis (R.outerNormalPairSumPullbackAxis N)

/-- Literal denominator below the pair-constant omega state. -/
def outerNormalConstantAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)) :=
  R.transportOuterPullbackAxis (R.outerNormalConstantPullbackAxis N)

theorem outerNormalPairSumAxis_le_outerOmegaPairSumAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.outerNormalPairSumAxis N ≤ R.outerOmegaPairSumAxis N :=
  R.outerNormalPairSum_le_outerOmegaPairSum N

theorem outerNormalConstantAxis_le_outerOmegaConstantAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    R.outerNormalConstantAxis N ≤ R.outerOmegaConstantAxis N :=
  R.outerNormalConstant_le_outerOmegaConstant N

end DegreeTwoPairTopTowerRealization
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
