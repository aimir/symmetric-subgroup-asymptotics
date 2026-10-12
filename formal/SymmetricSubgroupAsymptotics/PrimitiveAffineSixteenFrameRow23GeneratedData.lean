import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow23InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow23TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow23GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow23TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow23TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow23TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow23InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow23InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow23InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow23TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow23InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow23TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow23InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow23TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow23TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow23TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 5
  ambient := PrimitiveAffineSixteenFrameRow23TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow23TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow23InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow23InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow23InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow23InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow23InducedBinding.representative_mul_generator
  classCount := 24
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow23TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow23TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 16
  NormalGeneratorIndex := Fin 8
  stateGenerators := PrimitiveAffineSixteenFrameRow23NormalCertificate.stateGenerators
  topSlots := 2
  topRegistry := PrimitiveAffineSixteenFrameRow23TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow23InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow23InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow23InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr PrimitiveAffineSixteenFrameRow23InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow23InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow23InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow23OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow23InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow23OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 2 + 5 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow23GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
