import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow11InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow11TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow11GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow11TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow11TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow11TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow11InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow11InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow11InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow11TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow11InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow11TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow11InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow11TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow11TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow11TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 5
  ambient := PrimitiveAffineSixteenFrameRow11TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow11TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow11InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow11InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow11InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow11InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow11InducedBinding.representative_mul_generator
  classCount := 36
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow11TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow11TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 41
  NormalGeneratorIndex := Fin 8
  stateGenerators := PrimitiveAffineSixteenFrameRow11NormalCertificate.stateGenerators
  topSlots := 2
  topRegistry := PrimitiveAffineSixteenFrameRow11TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow11InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow11InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow11InducedBinding.sourceLocalMap_surjective
  local_card := Or.inl PrimitiveAffineSixteenFrameRow11InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow11InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow11InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow11OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow11InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow11OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 2 + 6 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow11GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
