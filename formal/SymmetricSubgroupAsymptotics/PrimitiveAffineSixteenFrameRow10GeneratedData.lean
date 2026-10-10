import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow10GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow10TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow10TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow10TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow10InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow10InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow10InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow10TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow10InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow10TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow10InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow10TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow10TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow10TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 3
  ambient := PrimitiveAffineSixteenFrameRow10TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow10TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow10InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow10InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow10InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow10InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow10InducedBinding.representative_mul_generator
  classCount := 14
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow10TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow10TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 7
  NormalGeneratorIndex := Fin 7
  stateGenerators := PrimitiveAffineSixteenFrameRow10NormalCertificate.stateGenerators
  topSlots := 1
  topRegistry := PrimitiveAffineSixteenFrameRow10TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow10InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow10InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow10InducedBinding.sourceLocalMap_surjective
  local_card := Or.inl PrimitiveAffineSixteenFrameRow10InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow10InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow10InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow10OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow10InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow10OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 1 + 6 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow10GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
