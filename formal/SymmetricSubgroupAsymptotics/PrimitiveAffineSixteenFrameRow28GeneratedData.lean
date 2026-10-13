import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow28InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow28TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow28GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow28TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow28TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow28TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow28InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow28InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow28InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow28TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow28InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow28TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow28InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow28TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow28TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow28TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 4
  ambient := PrimitiveAffineSixteenFrameRow28TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow28TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow28InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow28InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow28InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow28InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow28InducedBinding.representative_mul_generator
  classCount := 29
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow28TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow28TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 14
  NormalGeneratorIndex := Fin 9
  stateGenerators := PrimitiveAffineSixteenFrameRow28NormalCertificate.stateGenerators
  topSlots := 2
  topRegistry := PrimitiveAffineSixteenFrameRow28TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow28InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow28InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow28InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr PrimitiveAffineSixteenFrameRow28InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow28InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow28InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow28OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow28InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow28OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 2 + 3 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow28GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
