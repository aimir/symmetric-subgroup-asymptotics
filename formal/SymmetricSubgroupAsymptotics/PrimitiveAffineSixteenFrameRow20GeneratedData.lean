import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow20GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow20TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow20TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow20TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow20InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow20InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow20InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow20TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow20InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow20TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow20InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow20TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow20TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow20TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 5
  ambient := PrimitiveAffineSixteenFrameRow20TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow20TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow20InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow20InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow20InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow20InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow20InducedBinding.representative_mul_generator
  classCount := 12
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow20TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow20TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 8
  NormalGeneratorIndex := Fin 7
  stateGenerators := PrimitiveAffineSixteenFrameRow20NormalCertificate.stateGenerators
  topSlots := 1
  topRegistry := PrimitiveAffineSixteenFrameRow20TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow20InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow20InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow20InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr PrimitiveAffineSixteenFrameRow20InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow20InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow20InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow20OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow20InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow20OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 1 + 5 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow20GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
