import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameGeneratedLocalNormalTable
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop17TopRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistry

/-!
# Shared generated data for eight-frame top 17

Rows 26 share one literal transitive top and one point stabilizer.
Only their local quotient maps and binary modules remain row-varying.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineEightFrameTop17GeneratedData

abbrev Source := PrimitiveAffineEightFrameTop17TopCertificate.Source
local instance sourceGroup : Group Source :=
  PrimitiveAffineEightFrameTop17TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range PrimitiveAffineEightFrameTop17TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineEightFrameRow26InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineEightFrameRow26InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineEightFrameRow26InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineEightFrameTop17TopCertificate.originalEquiv x :
        LiteralAction) : Equiv.Perm (Fin 8))) (0 : Fin 8) = 0) := by
  intro x
  change PrimitiveAffineEightFrameRow26InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineEightFrameTop17TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineEightFrameRow26InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 8) :=
  GeneratedTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineEightFrameTop17TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineEightFrameTop17TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineEightFrameTop17TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 6
  ambient := PrimitiveAffineEightFrameTop17TopCertificate.ambient
  ambient_full := PrimitiveAffineEightFrameTop17TopCertificate.ambient_full
  representative := PrimitiveAffineEightFrameRow26InducedBinding.representative
  representative_factor := PrimitiveAffineEightFrameRow26InducedBinding.representative_factor
  next := PrimitiveAffineEightFrameRow26InducedBinding.next
  twist := PrimitiveAffineEightFrameRow26InducedBinding.twist
  representative_mul_generator := PrimitiveAffineEightFrameRow26InducedBinding.representative_mul_generator
  classCount := 20
  conjugacyRepresentative := PrimitiveAffineEightFrameTop17TopCertificate.representative
  conjugacyCover := PrimitiveAffineEightFrameTop17TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 11
  NormalGeneratorIndex := Fin 7
  stateGenerators := PrimitiveAffineEightFrameTop17NormalCertificate.stateGenerators
  topRegistry := PrimitiveAffineEightFrameTop17TopRegistry.registry

noncomputable def row26Data : GeneratedRowData topData where
  LocalTarget := PrimitiveAffineEightFrameRow26InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineEightFrameRow26InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineEightFrameRow26InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr PrimitiveAffineEightFrameRow26InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineEightFrameRow26InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineEightFrameRow26InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineEightFrameRow26ModuleRepresentation.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineEightFrameRow26InducedBinding.representation_generator_formula
  moduleRegistry := PrimitiveAffineEightFrameRow26ModuleRegistry.registry

end PrimitiveAffineEightFrameTop17GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
