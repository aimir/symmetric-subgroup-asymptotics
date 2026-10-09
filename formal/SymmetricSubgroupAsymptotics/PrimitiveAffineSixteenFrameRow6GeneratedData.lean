import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow6GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow6TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow6TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow6TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow6InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow6InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow6InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow6TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow6InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow6TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow6InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow6TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow6TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow6TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 4
  ambient := PrimitiveAffineSixteenFrameRow6TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow6TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow6InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow6InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow6InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow6InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow6InducedBinding.representative_mul_generator
  classCount := 9
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow6TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow6TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 9
  NormalGeneratorIndex := Fin 6
  stateGenerators := PrimitiveAffineSixteenFrameRow6NormalCertificate.stateGenerators
  topSlots := 0
  topRegistry := PrimitiveAffineSixteenFrameRow6TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow6InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow6InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow6InducedBinding.sourceLocalMap_surjective
  local_card := Or.inl PrimitiveAffineSixteenFrameRow6InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow6InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow6InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow6OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow6InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow6OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 0 + 10 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow6GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
