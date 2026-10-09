import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow3InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow3TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow3GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow3TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow3TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow3TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow3InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow3InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow3InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow3TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow3InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow3TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow3InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow3TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow3TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow3TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 3
  ambient := PrimitiveAffineSixteenFrameRow3TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow3TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow3InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow3InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow3InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow3InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow3InducedBinding.representative_mul_generator
  classCount := 10
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow3TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow3TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 7
  NormalGeneratorIndex := Fin 5
  stateGenerators := PrimitiveAffineSixteenFrameRow3NormalCertificate.stateGenerators
  topSlots := 1
  topRegistry := PrimitiveAffineSixteenFrameRow3TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow3InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow3InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow3InducedBinding.sourceLocalMap_surjective
  local_card := Or.inl PrimitiveAffineSixteenFrameRow3InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow3InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow3InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow3OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow3InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow3OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 1 + 6 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow3GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
