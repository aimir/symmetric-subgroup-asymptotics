import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow5GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow5TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow5TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow5TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow5InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow5InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow5InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow5TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow5InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow5TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow5InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow5TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow5TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow5TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 3
  ambient := PrimitiveAffineSixteenFrameRow5TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow5TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow5InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow5InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow5InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow5InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow5InducedBinding.representative_mul_generator
  classCount := 10
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow5TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow5TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 7
  NormalGeneratorIndex := Fin 5
  stateGenerators := PrimitiveAffineSixteenFrameRow5NormalCertificate.stateGenerators
  topSlots := 1
  topRegistry := PrimitiveAffineSixteenFrameRow5TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow5InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow5InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow5InducedBinding.sourceLocalMap_surjective
  local_card := Or.inl PrimitiveAffineSixteenFrameRow5InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow5InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow5InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow5OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow5InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow5OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 1 + 6 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow5GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
