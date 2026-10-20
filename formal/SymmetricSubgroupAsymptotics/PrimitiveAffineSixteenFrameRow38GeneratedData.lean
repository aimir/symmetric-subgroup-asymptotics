import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow38InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow38TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow38GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow38TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow38TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow38TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow38InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow38InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow38InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow38TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow38InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow38TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow38InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow38TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow38TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow38TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 3
  ambient := PrimitiveAffineSixteenFrameRow38TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow38TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow38InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow38InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow38InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow38InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow38InducedBinding.representative_mul_generator
  classCount := 19
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow38TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow38TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 5
  NormalGeneratorIndex := Fin 7
  stateGenerators := PrimitiveAffineSixteenFrameRow38NormalCertificate.stateGenerators
  topSlots := 0
  topRegistry := PrimitiveAffineSixteenFrameRow38TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow38InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow38InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow38InducedBinding.sourceLocalMap_surjective
  local_card := Or.inl PrimitiveAffineSixteenFrameRow38InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow38InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow38InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow38OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow38InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow38OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 0 + 2 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow38GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
