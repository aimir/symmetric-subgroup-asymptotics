import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow34InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow34TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow34GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow34TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow34TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow34TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow34InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow34InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow34InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow34TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow34InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow34TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow34InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow34TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow34TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow34TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 5
  ambient := PrimitiveAffineSixteenFrameRow34TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow34TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow34InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow34InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow34InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow34InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow34InducedBinding.representative_mul_generator
  classCount := 16
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow34TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow34TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 11
  NormalGeneratorIndex := Fin 7
  stateGenerators := PrimitiveAffineSixteenFrameRow34NormalCertificate.stateGenerators
  topSlots := 2
  topRegistry := PrimitiveAffineSixteenFrameRow34TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow34InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow34InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow34InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr PrimitiveAffineSixteenFrameRow34InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow34InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow34InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow34OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow34InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow34OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 2 + 2 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow34GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
