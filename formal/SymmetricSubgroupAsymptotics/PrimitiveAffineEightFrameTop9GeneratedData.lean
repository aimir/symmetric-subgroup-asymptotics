import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameGeneratedLocalNormalTable
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop9TopRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow14InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow14ModuleRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistry

/-!
# Shared generated data for eight-frame top 9

Rows 14, 15, 16, 17 share one literal transitive top and one point stabilizer.
Only their local quotient maps and binary modules remain row-varying.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineEightFrameTop9GeneratedData

abbrev Source := PrimitiveAffineEightFrameTop9TopCertificate.Source
local instance sourceGroup : Group Source :=
  PrimitiveAffineEightFrameTop9TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range PrimitiveAffineEightFrameTop9TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineEightFrameRow14InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineEightFrameRow14InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineEightFrameRow14InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineEightFrameTop9TopCertificate.originalEquiv x :
        LiteralAction) : Equiv.Perm (Fin 8))) (0 : Fin 8) = 0) := by
  intro x
  change PrimitiveAffineEightFrameRow14InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineEightFrameTop9TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineEightFrameRow14InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 8) :=
  GeneratedTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineEightFrameTop9TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineEightFrameTop9TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineEightFrameTop9TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 8
  ambient := PrimitiveAffineEightFrameTop9TopCertificate.ambient
  ambient_full := PrimitiveAffineEightFrameTop9TopCertificate.ambient_full
  representative := PrimitiveAffineEightFrameRow14InducedBinding.representative
  representative_factor := PrimitiveAffineEightFrameRow14InducedBinding.representative_factor
  next := PrimitiveAffineEightFrameRow14InducedBinding.next
  twist := PrimitiveAffineEightFrameRow14InducedBinding.twist
  representative_mul_generator := PrimitiveAffineEightFrameRow14InducedBinding.representative_mul_generator
  classCount := 13
  conjugacyRepresentative := PrimitiveAffineEightFrameTop9TopCertificate.representative
  conjugacyCover := PrimitiveAffineEightFrameTop9TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 5
  NormalGeneratorIndex := Fin 6
  stateGenerators := PrimitiveAffineEightFrameTop9NormalCertificate.stateGenerators
  topRegistry := PrimitiveAffineEightFrameTop9TopRegistry.registry

noncomputable def row14Data : GeneratedRowData topData where
  LocalTarget := PrimitiveAffineEightFrameRow14InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineEightFrameRow14InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineEightFrameRow14InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr PrimitiveAffineEightFrameRow14InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineEightFrameRow14InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineEightFrameRow14InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineEightFrameRow14ModuleRepresentation.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineEightFrameRow14InducedBinding.representation_generator_formula
  moduleRegistry := PrimitiveAffineEightFrameRow14ModuleRegistry.registry

noncomputable def row15Data : GeneratedRowData topData where
  LocalTarget := PrimitiveAffineEightFrameRow15InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineEightFrameRow15InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineEightFrameRow15InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr PrimitiveAffineEightFrameRow15InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineEightFrameRow15InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineEightFrameRow15InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineEightFrameRow15ModuleRepresentation.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineEightFrameRow15InducedBinding.representation_generator_formula
  moduleRegistry := PrimitiveAffineEightFrameRow15ModuleRegistry.registry

noncomputable def row16Data : GeneratedRowData topData where
  LocalTarget := PrimitiveAffineEightFrameRow16InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineEightFrameRow16InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineEightFrameRow16InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr PrimitiveAffineEightFrameRow16InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineEightFrameRow16InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineEightFrameRow16InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineEightFrameRow16ModuleRepresentation.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineEightFrameRow16InducedBinding.representation_generator_formula
  moduleRegistry := PrimitiveAffineEightFrameRow16ModuleRegistry.registry

noncomputable def row17Data : GeneratedRowData topData where
  LocalTarget := PrimitiveAffineEightFrameRow17InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineEightFrameRow17InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineEightFrameRow17InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr PrimitiveAffineEightFrameRow17InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineEightFrameRow17InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineEightFrameRow17InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineEightFrameRow17ModuleRepresentation.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineEightFrameRow17InducedBinding.representation_generator_formula
  moduleRegistry := PrimitiveAffineEightFrameRow17ModuleRegistry.registry

end PrimitiveAffineEightFrameTop9GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
