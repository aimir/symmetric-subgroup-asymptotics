import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow24GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow24TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow24TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow24TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow24InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow24InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow24InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow24TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow24InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow24TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow24InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow24TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow24TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow24TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 4
  ambient := PrimitiveAffineSixteenFrameRow24TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow24TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow24InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow24InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow24InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow24InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow24InducedBinding.representative_mul_generator
  classCount := 19
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow24TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow24TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 8
  NormalGeneratorIndex := Fin 8
  stateGenerators := PrimitiveAffineSixteenFrameRow24NormalCertificate.stateGenerators
  topSlots := 1
  topRegistry := PrimitiveAffineSixteenFrameRow24TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow24InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow24InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow24InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr PrimitiveAffineSixteenFrameRow24InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow24InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow24InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow24OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow24InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow24OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 1 + 5 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow24GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
