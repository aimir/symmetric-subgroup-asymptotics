import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow12InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow12TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow12GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow12TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow12TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow12TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow12InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow12InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow12InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow12TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow12InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow12TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow12InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow12TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow12TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow12TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 3
  ambient := PrimitiveAffineSixteenFrameRow12TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow12TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow12InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow12InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow12InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow12InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow12InducedBinding.representative_mul_generator
  classCount := 28
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow12TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow12TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 15
  NormalGeneratorIndex := Fin 8
  stateGenerators := PrimitiveAffineSixteenFrameRow12NormalCertificate.stateGenerators
  topSlots := 2
  topRegistry := PrimitiveAffineSixteenFrameRow12TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow12InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow12InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow12InducedBinding.sourceLocalMap_surjective
  local_card := Or.inl PrimitiveAffineSixteenFrameRow12InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow12InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow12InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow12OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow12InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow12OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 2 + 6 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow12GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
