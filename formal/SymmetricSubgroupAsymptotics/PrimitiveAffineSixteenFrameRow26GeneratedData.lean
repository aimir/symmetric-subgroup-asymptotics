import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow26GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow26TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow26TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow26TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow26InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow26InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow26InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow26TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow26InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow26TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow26InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow26TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow26TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow26TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 4
  ambient := PrimitiveAffineSixteenFrameRow26TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow26TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow26InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow26InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow26InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow26InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow26InducedBinding.representative_mul_generator
  classCount := 19
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow26TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow26TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 8
  NormalGeneratorIndex := Fin 8
  stateGenerators := PrimitiveAffineSixteenFrameRow26NormalCertificate.stateGenerators
  topSlots := 1
  topRegistry := PrimitiveAffineSixteenFrameRow26TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow26InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow26InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow26InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr PrimitiveAffineSixteenFrameRow26InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow26InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow26InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow26OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow26InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow26OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 1 + 3 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow26GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
