import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow21InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow21TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow21GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow21TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow21TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow21TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow21InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow21InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow21InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow21TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow21InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow21TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow21InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow21TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow21TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow21TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 5
  ambient := PrimitiveAffineSixteenFrameRow21TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow21TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow21InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow21InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow21InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow21InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow21InducedBinding.representative_mul_generator
  classCount := 16
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow21TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow21TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 13
  NormalGeneratorIndex := Fin 7
  stateGenerators := PrimitiveAffineSixteenFrameRow21NormalCertificate.stateGenerators
  topSlots := 2
  topRegistry := PrimitiveAffineSixteenFrameRow21TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow21InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow21InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow21InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr PrimitiveAffineSixteenFrameRow21InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow21InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow21InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow21OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow21InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow21OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 2 + 3 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow21GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
