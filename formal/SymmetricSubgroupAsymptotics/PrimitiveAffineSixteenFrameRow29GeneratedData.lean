import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow29InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow29TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow29GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow29TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow29TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow29TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow29InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow29InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow29InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow29TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow29InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow29TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow29InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow29TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow29TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow29TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 4
  ambient := PrimitiveAffineSixteenFrameRow29TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow29TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow29InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow29InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow29InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow29InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow29InducedBinding.representative_mul_generator
  classCount := 44
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow29TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow29TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 13
  NormalGeneratorIndex := Fin 11
  stateGenerators := PrimitiveAffineSixteenFrameRow29NormalCertificate.stateGenerators
  topSlots := 1
  topRegistry := PrimitiveAffineSixteenFrameRow29TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow29InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow29InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow29InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr PrimitiveAffineSixteenFrameRow29InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow29InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow29InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow29OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow29InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow29OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 1 + 3 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow29GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
