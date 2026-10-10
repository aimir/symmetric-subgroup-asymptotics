import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow9InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow9TopSplitRegistry

/-! Generated shared top data and one row for a degree-sixteen finite frame. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow9GeneratedData

abbrev Source := PrimitiveAffineSixteenFrameRow9TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow9TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow9TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineSixteenFrameRow9InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineSixteenFrameRow9InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow9InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow9TopCertificate.originalEquiv x : LiteralAction) :
        Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow9InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow9TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow9InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow9TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineSixteenFrameRow9TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineSixteenFrameRow9TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 4
  ambient := PrimitiveAffineSixteenFrameRow9TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow9TopCertificate.ambient_full
  representative := PrimitiveAffineSixteenFrameRow9InducedBinding.representative
  representative_factor := PrimitiveAffineSixteenFrameRow9InducedBinding.representative_factor
  next := PrimitiveAffineSixteenFrameRow9InducedBinding.next
  twist := PrimitiveAffineSixteenFrameRow9InducedBinding.twist
  representative_mul_generator := PrimitiveAffineSixteenFrameRow9InducedBinding.representative_mul_generator
  classCount := 18
  conjugacyRepresentative := PrimitiveAffineSixteenFrameRow9TopCertificate.representative
  conjugacyCover := PrimitiveAffineSixteenFrameRow9TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 17
  NormalGeneratorIndex := Fin 7
  stateGenerators := PrimitiveAffineSixteenFrameRow9NormalCertificate.stateGenerators
  topSlots := 1
  topRegistry := PrimitiveAffineSixteenFrameRow9TopSplitRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := PrimitiveAffineSixteenFrameRow9InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineSixteenFrameRow9InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineSixteenFrameRow9InducedBinding.sourceLocalMap_surjective
  local_card := Or.inl PrimitiveAffineSixteenFrameRow9InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineSixteenFrameRow9InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineSixteenFrameRow9InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineSixteenFrameRow9OddNormalizerModule.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineSixteenFrameRow9InducedBinding.representation_generator_formula
  fixedWitness := PrimitiveAffineSixteenFrameRow9OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 1 + 6 ≤ 10
    omega

end PrimitiveAffineSixteenFrameRow9GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
