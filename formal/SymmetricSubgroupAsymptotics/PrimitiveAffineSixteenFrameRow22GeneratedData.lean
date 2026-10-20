import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow22InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow22TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow22GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow22TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow22TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow22TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow22InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow22InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow22InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow22TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow22InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow22TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow22InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow22TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow22TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow22TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 4
  ambient := PrimitiveAffineSixteenFrameRow22TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow22TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow22InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow22InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow22InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow22InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow22InducedBinding.representative_mul_generator
  classCount := 16
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow22TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow22TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 13
  NormalGeneratorIndex := Fin 7
  stateGenerators := PrimitiveAffineSixteenFrameRow22NormalCertificate.stateGenerators
  topSlots := 2
  topRegistry := PrimitiveAffineSixteenFrameRow22TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow22InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow22InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow22InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr PrimitiveAffineSixteenFrameRow22InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow22InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow22InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow22OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow22InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow22OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 2 + 3 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow22GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
