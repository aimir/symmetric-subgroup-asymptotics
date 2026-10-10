import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopTowerQuotient
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopTowerOmegaFiltration
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

/-- The first top acts on the pair coordinates through the selected literal
degree-eight top. -/
def outerTopToLiteral : R.frame.top.range →* D.top :=
  R.topEquiv.symm.toMonoidHom.comp R.secondFrame.top.rangeRestrict

theorem outerTopToLiteral_surjective :
    Function.Surjective R.outerTopToLiteral :=
  R.topEquiv.symm.surjective.comp
    R.secondFrame.top.rangeRestrict_surjective

/-- Descending two pulled-back axes and transporting them to the catalogue
top commutes with forming their nested quotient. -/
noncomputable def outerPullbackNestedQuotientEquiv
    (A B : Subrepresentation R.secondFrame.pulledBackCoordinateTopAction)
    (hAB : A ≤ B) :
    (nestedQuotientRepresentation A B hAB).Equiv
      ((nestedQuotientRepresentation
        (R.transportOuterPullbackAxis A)
        (R.transportOuterPullbackAxis B) hAB).comp
          R.outerTopToLiteral) :=
  Representation.Equiv.mk (LinearEquiv.refl _ _) (by
    intro g
    apply LinearMap.ext
    intro x
    obtain ⟨b, rfl⟩ :=
      (nestedSubrepresentation A B hAB).toSubmodule.mkQ_surjective x
    apply congrArg
      (nestedSubrepresentation
        (R.transportOuterPullbackAxis A)
        (R.transportOuterPullbackAxis B) hAB).toSubmodule.mkQ
    apply Subtype.ext
    change R.secondFrame.pulledBackCoordinateTopAction g b.1 =
      permutationFunctionRepresentation (ZMod 2) D.top (Fin t)
        (R.outerTopToLiteral g) b.1
    rw [R.module_action_eq, R.topEquiv.apply_symm_apply]
    rfl)

/-- The right endpoint of the outer exact sequence is the inflation of a
literal paired-eight state quotient. -/
noncomputable def outerPairSumQuotientEquiv
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (nestedQuotientRepresentation
      (R.outerNormalPairSumPullbackAxis N)
      (R.outerOmegaPairSumPullbackAxis N)
      (R.outerNormalPairSum_le_outerOmegaPairSum N)).Equiv
      ((nestedQuotientRepresentation
        (R.outerNormalPairSumAxis N)
        (R.outerOmegaPairSumAxis N)
        (R.outerNormalPairSumAxis_le_outerOmegaPairSumAxis N)).comp
          R.outerTopToLiteral) :=
  R.outerPullbackNestedQuotientEquiv _ _ _

/-- The kernel endpoint of the outer exact sequence is likewise the
inflation of a literal paired-eight state quotient. -/
noncomputable def outerConstantQuotientEquiv
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (nestedQuotientRepresentation
      (R.outerNormalConstantPullbackAxis N)
      (R.outerOmegaConstantPullbackAxis N)
      (R.outerNormalConstant_le_outerOmegaConstant N)).Equiv
      ((nestedQuotientRepresentation
        (R.outerNormalConstantAxis N)
        (R.outerOmegaConstantAxis N)
        (R.outerNormalConstantAxis_le_outerOmegaConstantAxis N)).comp
          R.outerTopToLiteral) :=
  R.outerPullbackNestedQuotientEquiv _ _ _

/-- The actual outer projection kernel, expressed as its exact image in the
first zero-cut representation. -/
abbrev rawKernelOmegaOuterZeroCutImage
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :=
  (R.rawKernelOmegaOuterIntertwiner N).range

/-- The injective outer coordinate map identifies the actual projection
kernel with its zero-cut image. -/
noncomputable def rawKernelOmegaOuterEquivZeroCutImage
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.rawKernelOmegaInnerImageIntertwiner N).ker.toRepresentation.Equiv
      (R.rawKernelOmegaOuterZeroCutImage N).toRepresentation := by
  let q := R.rawKernelOmegaOuterIntertwiner N
  let e := RepresentationHeadExact.rangeProjection q
  apply e.ofBijective
  constructor
  · intro x y hxy
    exact R.rawKernelOmegaOuterIntertwiner_injective N
      (congrArg Subtype.val hxy)
  · exact RepresentationHeadExact.rangeProjection_surjective q

/-- The underlying zero-cut image is exactly the previously computed image
of the retained first-kernel omega intersection. -/
theorem rawKernelOmegaOuterZeroCutImage_toSubmodule
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.rawKernelOmegaOuterZeroCutImage N).toSubmodule =
      LinearMap.range (R.outerOmegaZeroCutMap N) := by
  rw [← R.rawKernelOmegaOuterCoordinateMap_range_eq N]
  ext v
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨R.rawKernelOmegaInnerKernelEquivProjectionKernel N z, rfl⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨w, rfl⟩ :=
      (R.rawKernelOmegaInnerKernelEquivProjectionKernel N).surjective z
    exact ⟨w, rfl⟩

/-- The section-image form of the retained outer coordinate state. -/
abbrev outerOmegaSectionImage
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :=
  intertwinerImage
    R.frame.kernelTopPermutationSubrepresentation.toRepresentation
    (R.frame.sectionTopRepresentation N.1)
    (R.frame.sectionTopIntertwiner N.1)
    (nestedSubrepresentation (R.outerOmegaAxis N)
      R.frame.kernelTopPermutationSubrepresentation
      (R.outerOmegaAxis_le_kernelTop N))

/-- The zero-cut/section equivalence sends every retained kernel element to
its literal section coordinate. -/
@[simp] theorem zeroCutSectionEquiv_outerOmegaZeroCutMap
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (l : R.outerOmegaRetainedKernel N) :
    R.frame.zeroCutSectionEquiv N.1
        (R.outerOmegaZeroCutMap N (Additive.ofMul l)) =
      (R.frame.normalSpace N.1).mkQ
        (R.frame.kernelSpaceHom l.1).toAdd :=
  rfl

/-- The retained zero-cut range is carried exactly onto the actual section
image of `B/A`. -/
theorem outerOmegaZeroCutRange_map_eq_sectionImage
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (LinearMap.range (R.outerOmegaZeroCutMap N)).map
        (R.frame.zeroCutSectionEquiv N.1).toLinearMap =
      (R.outerOmegaSectionImage N).toSubmodule := by
  ext v
  constructor
  · rintro ⟨a, ⟨l, rfl⟩, rfl⟩
    let b : R.frame.kernelTopPermutationSubrepresentation.toSubmodule :=
      (R.frame.kernelSpaceHom l.toMul.1).toAdd
    have hb : b.1 ∈ (R.outerOmegaAxis N).toSubmodule := by
      change R.frame.bits l.toMul.1 ∈
        R.frame.ambientAxis (R.rawKernelOmegaOriginalPreimage N)
      exact (R.frame.bits_mem_ambientAxis _ l.toMul.1).2 l.toMul.2
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    change b.1 ∈ (R.outerOmegaAxis N).toSubmodule at hb
    change b.1 ∈
      R.frame.ambientAxis (R.rawKernelOmegaOriginalPreimage N) at hb
    obtain ⟨l, hl, hlb⟩ := (R.frame.mem_ambientAxis _ b.1).1 hb
    let lOmega : R.outerOmegaRetainedKernel N := ⟨l, hl⟩
    refine ⟨R.outerOmegaZeroCutMap N (Additive.ofMul lOmega),
      ⟨Additive.ofMul lOmega, rfl⟩, ?_⟩
    rw [R.zeroCutSectionEquiv_outerOmegaZeroCutMap N lOmega]
    apply congrArg (R.frame.normalSpace N.1).mkQ
    apply Subtype.ext
    exact hlb

/-- The section image, with its action descended from the original quotient
through the first zero-cut base map. -/
def outerOmegaSectionImageOnOriginalQuotient
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation
      ((R.frame.sectionRepresentation N.1).comp
        (R.frame.zeroCutBase N.1)) where
  toSubmodule := (R.outerOmegaSectionImage N).toSubmodule
  apply_mem_toSubmodule q v hv := by
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective N.1 q
    change R.frame.sectionRepresentation N.1
        (QuotientGroup.mk' (R.frame.top.ker ⊔ N.1) u) v ∈
      (R.outerOmegaSectionImage N).toSubmodule
    rw [← R.frame.sectionTopQuotient_apply N.1 u]
    exact (R.outerOmegaSectionImage N).apply_mem_toSubmodule
      (R.frame.top.rangeRestrict u) hv

/-- Restricting the inflated zero-cut/section equivalence to the retained
images identifies the concrete outer kernel image with the corresponding
section image over the original quotient. -/
noncomputable def rawKernelOmegaOuterZeroCutImageEquivSectionImage
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.rawKernelOmegaOuterZeroCutImage N).toRepresentation.Equiv
      (R.outerOmegaSectionImageOnOriginalQuotient N).toRepresentation := by
  let e := R.frame.zeroCutSectionCompEquiv N.1
    (R.frame.zeroCutBase N.1)
  let f : (R.rawKernelOmegaOuterZeroCutImage N).toRepresentation.
      IntertwiningMap
      (R.outerOmegaSectionImageOnOriginalQuotient N).toRepresentation where
    toLinearMap :=
      (e.toLinearEquiv.toLinearMap.comp
        (R.rawKernelOmegaOuterZeroCutImage N).toSubmodule.subtype).codRestrict
          (R.outerOmegaSectionImageOnOriginalQuotient N).toSubmodule
          (fun z ↦ by
            rw [← R.outerOmegaZeroCutRange_map_eq_sectionImage N]
            exact ⟨z.1, by
              rw [← R.rawKernelOmegaOuterZeroCutImage_toSubmodule N]
              exact z.2, rfl⟩)
    isIntertwining' := by
      intro q
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      exact LinearMap.congr_fun (e.isIntertwining' q) z.1
  apply f.ofBijective
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val hxy)
  · rintro ⟨v, hv⟩
    rw [← R.outerOmegaZeroCutRange_map_eq_sectionImage N] at hv
    obtain ⟨a, ha, hav⟩ := hv
    have haImage : a ∈
        (R.rawKernelOmegaOuterZeroCutImage N).toSubmodule := by
      rw [R.rawKernelOmegaOuterZeroCutImage_toSubmodule N]
      exact ha
    exact ⟨⟨a, haImage⟩, Subtype.ext hav⟩

/-- The actual outer projection kernel is therefore equivalent to the
retained first-frame section image, both carrying the original quotient
action. -/
noncomputable def rawKernelOmegaOuterEquivSectionImage
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (R.rawKernelOmegaInnerImageIntertwiner N).ker.toRepresentation.Equiv
      (R.outerOmegaSectionImageOnOriginalQuotient N).toRepresentation :=
  (R.rawKernelOmegaOuterEquivZeroCutImage N).trans
    (R.rawKernelOmegaOuterZeroCutImageEquivSectionImage N)

end DegreeTwoPairTopTowerRealization
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
