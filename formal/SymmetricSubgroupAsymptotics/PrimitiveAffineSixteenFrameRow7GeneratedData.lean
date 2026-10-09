import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow7InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow7TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow7GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow7TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow7TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow7TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow7InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow7InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow7InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow7TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow7InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow7TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow7InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow7TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow7TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow7TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 4
  ambient := PrimitiveAffineSixteenFrameRow7TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow7TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow7InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow7InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow7InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow7InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow7InducedBinding.representative_mul_generator
  classCount := 17
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow7TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow7TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 16
  NormalGeneratorIndex := Fin 6
  stateGenerators := PrimitiveAffineSixteenFrameRow7NormalCertificate.stateGenerators
  topSlots := 2
  topRegistry := PrimitiveAffineSixteenFrameRow7TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow7InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow7InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow7InducedBinding.sourceLocalMap_surjective
  local_card := Or.inl PrimitiveAffineSixteenFrameRow7InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow7InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow7InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow7OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow7InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow7OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 2 + 6 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow7GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
