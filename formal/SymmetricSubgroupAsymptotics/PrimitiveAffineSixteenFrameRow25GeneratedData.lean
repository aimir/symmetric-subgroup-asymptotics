import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow25InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow25TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow25GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow25TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow25TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow25TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow25InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow25InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow25InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow25TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow25InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow25TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow25InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow25TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow25TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow25TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 4
  ambient := PrimitiveAffineSixteenFrameRow25TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow25TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow25InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow25InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow25InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow25InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow25InducedBinding.representative_mul_generator
  classCount := 24
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow25TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow25TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 14
  NormalGeneratorIndex := Fin 8
  stateGenerators := PrimitiveAffineSixteenFrameRow25NormalCertificate.stateGenerators
  topSlots := 1
  topRegistry := PrimitiveAffineSixteenFrameRow25TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow25InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow25InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow25InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr PrimitiveAffineSixteenFrameRow25InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow25InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow25InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow25OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow25InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow25OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 1 + 3 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow25GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
