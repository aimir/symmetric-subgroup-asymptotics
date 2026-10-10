import SymmetricSubgroupAsymptotics.ActualWreathAffineCapacityUniform
import SymmetricSubgroupAsymptotics.BinaryPairFrameSignFiberHalfSix
import SymmetricSubgroupAsymptotics.BinaryPairFrameTernaryUniformGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeHighSignRepresentation

/-!
# Capacity three in the eighteen-block, three-sign cell

Three realized signs on eighteen block coordinates give three transitive
sign fibres, each of size six.  Tracey's half-induced theorem supplies
three generators on each fibre, and the literal isotype assembly preserves
that common bound.  Scalar transport then sharpens the actual affine joint
capacity to three while retaining its fixed-top coefficient.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace BinaryPairFrame

variable {X I : Type} {G : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame G I)

/-- At eighteen coordinates with exactly three realized signs, every
invariant submodule of the signed contragredient has three generators. -/
theorem ternarySignedRepresentation_dual_uniform_three_of_eighteen_three_signs
    [Finite X] [Finite I] [Nonempty I]
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (htrans : MulAction.IsPretransitive G X)
    (heighteen : Nat.card I = 18)
    (hthree : Nat.card (CoordinateSign F) = 3) :
    UniformSubrepresentationGeneratorBound
      (ternarySignedRepresentation F).dual 3 := by
  apply ternarySignedRepresentation_dual_uniformSubrepresentationGeneratorBound
    F 3 htrans
  intro chi
  let i := coordinateSignRepresentative F chi
  have hproduct := coordinateSign_count_mul_fibre_card F htrans i
  have heq : coordinateSign F i = chi :=
    coordinateSignRepresentative_spec F chi
  have hcard : Nat.card {j : I // coordinateSign F j = chi} = 6 := by
    rw [hthree, heighteen, heq] at hproduct
    omega
  exact signFiber_uniformSubrepresentationGeneratorBound_three_of_card_six
    F hTraceyHalf htrans chi hcard

end BinaryPairFrame

namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

open OddMarkerTernaryChart

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance threeSignCapacityPrimeFact : Fact P.p.Prime :=
  (chart block P).primeFact

/-- Native-field form of the three-generator signed-module theorem. -/
theorem degreeThreeNativeSignedRepresentation_dual_uniform_three_sign
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6)
    (heighteen : Nat.card block.Points = 18)
    (hthree : Nat.card (BinaryPairFrame.CoordinateSign
      (degreeThreeSignedQuotientPairFrame block P hr)) = 3) :
    UniformSubrepresentationGeneratorBound
      (degreeThreeNativeSignedRepresentation block P hr).dual 3 := by
  let F := degreeThreeSignedQuotientPairFrame block P hr
  have htrans := degreeThreeSignedQuotientRange_pretransitive
    block P hr hcomponent
  have hgeneric :=
    BinaryPairFrame.ternarySignedRepresentation_dual_uniform_three_of_eighteen_three_signs
      F hTraceyHalf htrans heighteen hthree
  have hp : P.p = 3 := (degreeThree_translation_prime_dim block P hr).1
  cases P
  subst_vars
  simpa [degreeThreeNativeSignedRepresentation,
    degreeThreeNativeSignRepresentation, degreeThreeNativeSignScalar,
    degreeThreeScalarFieldEquiv] using hgeneric

/-- The actual quotient translation contragredient inherits the bound
through the dual of the scalar-coordinate inclusion. -/
theorem degreeThreeTranslationQuotient_dual_uniform_three_sign
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6)
    (heighteen : Nat.card block.Points = 18)
    (hthree : Nat.card (BinaryPairFrame.CoordinateSign
      (degreeThreeSignedQuotientPairFrame block P hr)) = 3) :
    UniformSubrepresentationGeneratorBound
      ((elementaryChart block P).quotientRepresentation.ρ).dual 3 := by
  have hfull := degreeThreeNativeSignedRepresentation_dual_uniform_three_sign
    block P hTraceyHalf hr hcomponent heighteen hthree
  let f := degreeThreeTranslationScalarIntertwiner block P hr
  have hf : Function.Injective f :=
    degreeThreeTranslationScalarIntertwiner_injective block P hr
  have hhelper : UniformSubrepresentationGeneratorBound
      (degreeThreeElementaryQuotientRepresentation block P).dual 3 := by
    have hpull : UniformSubrepresentationGeneratorBound
        (Representation.dual
          ((degreeThreeNativeSignedRepresentation block P hr).comp
            (degreeThreeSignedQuotientRangeEquiv block P).toMonoidHom)) 3 := by
      have h := hfull.comp_of_surjective
        (degreeThreeNativeSignedRepresentation block P hr).dual
        (degreeThreeSignedQuotientRangeEquiv block P).toMonoidHom
        (degreeThreeSignedQuotientRangeEquiv block P).surjective
      convert h using 1
      apply MonoidHom.ext
      intro q
      apply LinearMap.ext
      intro ell
      apply LinearMap.ext
      intro v
      simp [Representation.dual, map_inv]
    apply hpull.of_surjective (RepresentationHeadExact.dualMap f)
    exact LinearMap.dualMap_surjective_of_injective hf
  simpa [degreeThreeElementaryQuotientRepresentation, elementaryChart] using hhelper

/-- Pull the quotient bound back to the affine group representation used
by the actual-wreath capacity construction. -/
theorem degreeThreeActualAmbient_dual_uniform_three_sign
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6)
    (heighteen : Nat.card block.Points = 18)
    (hthree : Nat.card (BinaryPairFrame.CoordinateSign
      (degreeThreeSignedQuotientPairFrame block P hr)) = 3) :
    UniformSubrepresentationGeneratorBound
      (ActualWreathAffineCapacity.ambientRepresentation
        (initialState hTraceyPerm block) (localMap block P)
        (localTranslationChart block P)).dual 3 := by
  have hquot := degreeThreeTranslationQuotient_dual_uniform_three_sign
    block P hTraceyHalf hr hcomponent heighteen hthree
  have hpull := hquot.comp_of_surjective
    ((elementaryChart block P).quotientRepresentation.ρ).dual
    (QuotientGroup.mk' (E block P))
    (QuotientGroup.mk'_surjective (E block P))
  simpa only [Representation.dual_apply,
    MonoidHom.comp_apply, map_inv,
    ActualWreathAffineCapacity.ambientRepresentation,
    initialState, localTranslationChart, elementaryChart,
    ActualWreathAffineCapacity.E,
    PermutationalWreathProduct.Compression.kernelElementaryChart] using hpull

/-- Capacity-three joint record for the last low-sign post-four cell. -/
noncomputable def degreeThreeThreeSignJointCapacity
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6)
    (heighteen : Nat.card block.Points = 18)
    (hthree : Nat.card (BinaryPairFrame.CoordinateSign
      (degreeThreeSignedQuotientPairFrame block P hr)) = 3) :
    ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart := by
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  let H := translationLayerJointCapacity block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm
  let huniform := degreeThreeActualAmbient_dual_uniform_three_sign
    block P hTraceyHalf hTraceyPerm hr hcomponent heighteen hthree
  simpa only [S, C, H, initialState, localTranslationChart,
    elementaryChart, ActualWreathAffineCapacity.E,
    PermutationalWreathProduct.Compression.kernelElementaryChart] using
      ActualWreathAffineCapacity.jointCapacitySharpenTo_of_ambientDual_uniform
        S (localMap block P) C 3 H huniform

@[simp] theorem degreeThreeThreeSignJointCapacity_capacity
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6)
    (heighteen : Nat.card block.Points = 18)
    (hthree : Nat.card (BinaryPairFrame.CoordinateSign
      (degreeThreeSignedQuotientPairFrame block P hr)) = 3) :
    (degreeThreeThreeSignJointCapacity block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm hr hcomponent heighteen hthree).capacity = 3 := by
  simp [degreeThreeThreeSignJointCapacity]

theorem degreeThreeThreeSignJointCapacity_coefficient_eq
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6)
    (heighteen : Nat.card block.Points = 18)
    (hthree : Nat.card (BinaryPairFrame.CoordinateSign
      (degreeThreeSignedQuotientPairFrame block P hr)) = 3) :
    (degreeThreeThreeSignJointCapacity block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm hr hcomponent heighteen hthree).coefficient =
      (translationLayerJointCapacity block P hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm).coefficient := by
  simp [degreeThreeThreeSignJointCapacity]

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
