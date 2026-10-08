import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameGeneratedLocalNormalTable
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop10TopRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow18InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow18ModuleRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleRegistry

/-!
# Shared generated data for eight-frame top 10

Rows 18, 19 share one literal transitive top and one point stabilizer.
Only their local quotient maps and binary modules remain row-varying.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineEightFrameTop10GeneratedData

abbrev Source := PrimitiveAffineEightFrameTop10TopCertificate.Source
local instance sourceGroup : Group Source :=
  PrimitiveAffineEightFrameTop10TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range PrimitiveAffineEightFrameTop10TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineEightFrameRow18InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineEightFrameRow18InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineEightFrameRow18InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineEightFrameTop10TopCertificate.originalEquiv x :
        LiteralAction) : Equiv.Perm (Fin 8))) (0 : Fin 8) = 0) := by
  intro x
  change PrimitiveAffineEightFrameRow18InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineEightFrameTop10TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineEightFrameRow18InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 8) :=
  GeneratedTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineEightFrameTop10TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineEightFrameTop10TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineEightFrameTop10TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 9
  ambient := PrimitiveAffineEightFrameTop10TopCertificate.ambient
  ambient_full := PrimitiveAffineEightFrameTop10TopCertificate.ambient_full
  representative := PrimitiveAffineEightFrameRow18InducedBinding.representative
  representative_factor := PrimitiveAffineEightFrameRow18InducedBinding.representative_factor
  next := PrimitiveAffineEightFrameRow18InducedBinding.next
  twist := PrimitiveAffineEightFrameRow18InducedBinding.twist
  representative_mul_generator := PrimitiveAffineEightFrameRow18InducedBinding.representative_mul_generator
  classCount := 20
  conjugacyRepresentative := PrimitiveAffineEightFrameTop10TopCertificate.representative
  conjugacyCover := PrimitiveAffineEightFrameTop10TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 8
  NormalGeneratorIndex := Fin 7
  stateGenerators := PrimitiveAffineEightFrameTop10NormalCertificate.stateGenerators
  topRegistry := PrimitiveAffineEightFrameTop10TopRegistry.registry

noncomputable def row18Data : GeneratedRowData topData where
  LocalTarget := PrimitiveAffineEightFrameRow18InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineEightFrameRow18InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineEightFrameRow18InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr PrimitiveAffineEightFrameRow18InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineEightFrameRow18InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineEightFrameRow18InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineEightFrameRow18ModuleRepresentation.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineEightFrameRow18InducedBinding.representation_generator_formula
  moduleRegistry := PrimitiveAffineEightFrameRow18ModuleRegistry.registry

noncomputable def row19Data : GeneratedRowData topData where
  LocalTarget := PrimitiveAffineEightFrameRow19InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineEightFrameRow19InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineEightFrameRow19InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr PrimitiveAffineEightFrameRow19InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineEightFrameRow19InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineEightFrameRow19InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineEightFrameRow19InducedBinding.representation_generator_formula
  moduleRegistry := PrimitiveAffineEightFrameRow19ModuleRegistry.registry

end PrimitiveAffineEightFrameTop10GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
