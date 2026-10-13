import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow27InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow27TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow27GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow27TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow27TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow27TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow27InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow27InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow27InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow27TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow27InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow27TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow27InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow27TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow27TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow27TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 4
  ambient := PrimitiveAffineSixteenFrameRow27TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow27TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow27InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow27InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow27InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow27InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow27InducedBinding.representative_mul_generator
  classCount := 33
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow27TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow27TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 22
  NormalGeneratorIndex := Fin 9
  stateGenerators := PrimitiveAffineSixteenFrameRow27NormalCertificate.stateGenerators
  topSlots := 2
  topRegistry := PrimitiveAffineSixteenFrameRow27TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow27InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow27InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow27InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr PrimitiveAffineSixteenFrameRow27InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow27InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow27InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow27OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow27InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow27OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 2 + 3 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow27GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
