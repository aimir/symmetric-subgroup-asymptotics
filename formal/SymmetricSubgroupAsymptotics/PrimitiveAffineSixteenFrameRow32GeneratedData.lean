import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow32InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow32GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow31TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow31TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow31TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow32InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow32InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow32InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow31TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow32InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow31TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow32InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow31TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow31TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow31TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 4
  ambient := PrimitiveAffineSixteenFrameRow31TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow31TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow32InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow32InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow32InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow32InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow32InducedBinding.representative_mul_generator
  classCount := 14
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow31TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow31TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 7
  NormalGeneratorIndex := Fin 6
  stateGenerators := PrimitiveAffineSixteenFrameRow31NormalCertificate.stateGenerators
  topSlots := 1
  topRegistry := PrimitiveAffineSixteenFrameRow31TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow32InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow32InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow32InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr PrimitiveAffineSixteenFrameRow32InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow32InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow32InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow32OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow32InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow32OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 1 + 2 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow32GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
