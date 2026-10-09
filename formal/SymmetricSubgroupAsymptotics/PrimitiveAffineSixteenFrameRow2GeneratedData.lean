import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow2GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow2TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow2TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow2TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow2InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow2InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow2InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow2TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow2InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow2TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow2InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow2TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow2TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow2TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 3
  ambient := PrimitiveAffineSixteenFrameRow2TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow2TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow2InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow2InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow2InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow2InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow2InducedBinding.representative_mul_generator
  classCount := 8
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow2TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow2TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 4
  NormalGeneratorIndex := Fin 4
  stateGenerators := PrimitiveAffineSixteenFrameRow2NormalCertificate.stateGenerators
  topSlots := 0
  topRegistry := PrimitiveAffineSixteenFrameRow2TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow2InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow2InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow2InducedBinding.sourceLocalMap_surjective
  local_card := Or.inl PrimitiveAffineSixteenFrameRow2InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow2InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow2InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow2OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow2InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow2OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 0 + 10 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow2GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
