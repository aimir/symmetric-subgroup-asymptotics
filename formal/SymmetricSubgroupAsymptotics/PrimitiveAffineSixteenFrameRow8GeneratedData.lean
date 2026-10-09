import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow8InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow8TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow8GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow8TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow8TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow8TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow8InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow8InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow8InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow8TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow8InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow8TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow8InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow8TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow8TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow8TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 3
  ambient := PrimitiveAffineSixteenFrameRow8TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow8TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow8InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow8InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow8InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow8InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow8InducedBinding.representative_mul_generator
  classCount := 17
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow8TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow8TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 16
  NormalGeneratorIndex := Fin 6
  stateGenerators := PrimitiveAffineSixteenFrameRow8NormalCertificate.stateGenerators
  topSlots := 2
  topRegistry := PrimitiveAffineSixteenFrameRow8TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow8InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow8InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow8InducedBinding.sourceLocalMap_surjective
  local_card := Or.inl PrimitiveAffineSixteenFrameRow8InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow8InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow8InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow8OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow8InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow8OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 2 + 6 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow8GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
