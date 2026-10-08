import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameGeneratedLocalNormalTable
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop13TopRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistry

/-!
# Shared generated data for eight-frame top 13

Rows 22 share one literal transitive top and one point stabilizer.
Only their local quotient maps and binary modules remain row-varying.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineEightFrameTop13GeneratedData

abbrev Source := PrimitiveAffineEightFrameTop13TopCertificate.Source
local instance sourceGroup : Group Source :=
  PrimitiveAffineEightFrameTop13TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range PrimitiveAffineEightFrameTop13TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineEightFrameRow22InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineEightFrameRow22InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineEightFrameRow22InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineEightFrameTop13TopCertificate.originalEquiv x :
        LiteralAction) : Equiv.Perm (Fin 8))) (0 : Fin 8) = 0) := by
  intro x
  change PrimitiveAffineEightFrameRow22InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineEightFrameTop13TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineEightFrameRow22InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 8) :=
  GeneratedTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineEightFrameTop13TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineEightFrameTop13TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineEightFrameTop13TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 6
  ambient := PrimitiveAffineEightFrameTop13TopCertificate.ambient
  ambient_full := PrimitiveAffineEightFrameTop13TopCertificate.ambient_full
  representative := PrimitiveAffineEightFrameRow22InducedBinding.representative
  representative_factor := PrimitiveAffineEightFrameRow22InducedBinding.representative_factor
  next := PrimitiveAffineEightFrameRow22InducedBinding.next
  twist := PrimitiveAffineEightFrameRow22InducedBinding.twist
  representative_mul_generator := PrimitiveAffineEightFrameRow22InducedBinding.representative_mul_generator
  classCount := 16
  conjugacyRepresentative := PrimitiveAffineEightFrameTop13TopCertificate.representative
  conjugacyCover := PrimitiveAffineEightFrameTop13TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 8
  NormalGeneratorIndex := Fin 6
  stateGenerators := PrimitiveAffineEightFrameTop13NormalCertificate.stateGenerators
  topRegistry := PrimitiveAffineEightFrameTop13TopRegistry.registry

noncomputable def row22Data : GeneratedRowData topData where
  LocalTarget := PrimitiveAffineEightFrameRow22InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineEightFrameRow22InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineEightFrameRow22InducedBinding.sourceLocalMap_surjective
  local_card := Or.inl PrimitiveAffineEightFrameRow22InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineEightFrameRow22InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineEightFrameRow22InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineEightFrameRow22InducedBinding.representation_generator_formula
  moduleRegistry := PrimitiveAffineEightFrameRow22ModuleRegistry.registry

end PrimitiveAffineEightFrameTop13GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
