import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameGeneratedLocalNormalTable
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop16TopRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow25InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow25ModuleRegistry

/-!
# Shared generated data for eight-frame top 16

Rows 25 share one literal transitive top and one point stabilizer.
Only their local quotient maps and binary modules remain row-varying.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineEightFrameTop16GeneratedData

abbrev Source := PrimitiveAffineEightFrameTop16TopCertificate.Source
local instance sourceGroup : Group Source :=
  PrimitiveAffineEightFrameTop16TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range PrimitiveAffineEightFrameTop16TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineEightFrameRow25InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineEightFrameRow25InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineEightFrameRow25InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineEightFrameTop16TopCertificate.originalEquiv x :
        LiteralAction) : Equiv.Perm (Fin 8))) (0 : Fin 8) = 0) := by
  intro x
  change PrimitiveAffineEightFrameRow25InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineEightFrameTop16TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineEightFrameRow25InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 8) :=
  GeneratedTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineEightFrameTop16TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineEightFrameTop16TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineEightFrameTop16TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 5
  ambient := PrimitiveAffineEightFrameTop16TopCertificate.ambient
  ambient_full := PrimitiveAffineEightFrameTop16TopCertificate.ambient_full
  representative := PrimitiveAffineEightFrameRow25InducedBinding.representative
  representative_factor := PrimitiveAffineEightFrameRow25InducedBinding.representative_factor
  next := PrimitiveAffineEightFrameRow25InducedBinding.next
  twist := PrimitiveAffineEightFrameRow25InducedBinding.twist
  representative_mul_generator := PrimitiveAffineEightFrameRow25InducedBinding.representative_mul_generator
  classCount := 13
  conjugacyRepresentative := PrimitiveAffineEightFrameTop16TopCertificate.representative
  conjugacyCover := PrimitiveAffineEightFrameTop16TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 8
  NormalGeneratorIndex := Fin 6
  stateGenerators := PrimitiveAffineEightFrameTop16NormalCertificate.stateGenerators
  topRegistry := PrimitiveAffineEightFrameTop16TopRegistry.registry

noncomputable def row25Data : GeneratedRowData topData where
  LocalTarget := PrimitiveAffineEightFrameRow25InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineEightFrameRow25InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineEightFrameRow25InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr PrimitiveAffineEightFrameRow25InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineEightFrameRow25InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineEightFrameRow25InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineEightFrameRow25ModuleRepresentation.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineEightFrameRow25InducedBinding.representation_generator_formula
  moduleRegistry := PrimitiveAffineEightFrameRow25ModuleRegistry.registry

end PrimitiveAffineEightFrameTop16GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
