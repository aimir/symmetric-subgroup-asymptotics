import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow4GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow4TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow4TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow4TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow4InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow4InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow4InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow4TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow4InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow4TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow4InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow4TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow4TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow4TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 3
  ambient := PrimitiveAffineSixteenFrameRow4TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow4TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow4InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow4InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow4InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow4InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow4InducedBinding.representative_mul_generator
  classCount := 10
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow4TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow4TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 7
  NormalGeneratorIndex := Fin 5
  stateGenerators := PrimitiveAffineSixteenFrameRow4NormalCertificate.stateGenerators
  topSlots := 1
  topRegistry := PrimitiveAffineSixteenFrameRow4TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow4InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow4InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow4InducedBinding.sourceLocalMap_surjective
  local_card := Or.inl PrimitiveAffineSixteenFrameRow4InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow4InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow4InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow4OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow4InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow4OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 1 + 6 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow4GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
