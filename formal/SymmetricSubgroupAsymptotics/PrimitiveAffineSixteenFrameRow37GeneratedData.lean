import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow37GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow37TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow37TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow37TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow37InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow37InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow37InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow37TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow37InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow37TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow37InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow37TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow37TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow37TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 3
  ambient := PrimitiveAffineSixteenFrameRow37TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow37TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow37InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow37InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow37InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow37InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow37InducedBinding.representative_mul_generator
  classCount := 17
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow37TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow37TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 6
  NormalGeneratorIndex := Fin 7
  stateGenerators := PrimitiveAffineSixteenFrameRow37NormalCertificate.stateGenerators
  topSlots := 1
  topRegistry := PrimitiveAffineSixteenFrameRow37TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow37InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow37InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow37InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr PrimitiveAffineSixteenFrameRow37InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow37InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow37InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow37OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow37InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow37OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 1 + 2 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow37GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
