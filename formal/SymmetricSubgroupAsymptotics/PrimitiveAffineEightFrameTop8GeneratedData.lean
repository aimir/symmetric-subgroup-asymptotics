import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameGeneratedLocalNormalTable
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop8TopRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow10InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow10ModuleRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow11InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow11ModuleRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow13InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow13ModuleRegistry

/-!
# Shared generated data for eight-frame top 8

Rows 10--13 have one literal transitive top and one point stabilizer.  This
module binds that data once and retains only the four distinct local maps and
binary modules as row data.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineEightFrameTop8GeneratedData

abbrev Source := PrimitiveAffineEightFrameTop8TopCertificate.Source
local instance sourceGroup : Group Source :=
  PrimitiveAffineEightFrameTop8TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure
    (Set.range PrimitiveAffineEightFrameTop8TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineEightFrameRow10InducedBinding.sourceStabilizer

/-- Executable membership in the shared point stabilizer.  The originating
row exposes the predicate but keeps its instance local; grouped certificate
files need the same instance without importing any row-specific proof. -/
instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable
    (PrimitiveAffineEightFrameRow10InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineEightFrameRow10InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineEightFrameTop8TopCertificate.originalEquiv x :
        LiteralAction) : Equiv.Perm (Fin 8))) (0 : Fin 8) = 0) := by
  intro x
  change PrimitiveAffineEightFrameRow10InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineEightFrameTop8TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineEightFrameRow10InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 8) :=
  GeneratedTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction
    PrimitiveAffineEightFrameTop8TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv :=
    PrimitiveAffineEightFrameTop8TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction
      PrimitiveAffineEightFrameTop8TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 8
  ambient := PrimitiveAffineEightFrameTop8TopCertificate.ambient
  ambient_full := PrimitiveAffineEightFrameTop8TopCertificate.ambient_full
  representative := PrimitiveAffineEightFrameRow10InducedBinding.representative
  representative_factor :=
    PrimitiveAffineEightFrameRow10InducedBinding.representative_factor
  next := PrimitiveAffineEightFrameRow10InducedBinding.next
  twist := PrimitiveAffineEightFrameRow10InducedBinding.twist
  representative_mul_generator :=
    PrimitiveAffineEightFrameRow10InducedBinding.representative_mul_generator
  classCount := 16
  conjugacyRepresentative :=
    PrimitiveAffineEightFrameTop8TopCertificate.representative
  conjugacyCover :=
    PrimitiveAffineEightFrameTop8TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 11
  NormalGeneratorIndex := Fin 6
  stateGenerators := PrimitiveAffineEightFrameTop8NormalCertificate.stateGenerators
  topRegistry := PrimitiveAffineEightFrameTop8TopRegistry.registry

noncomputable def row10Data : GeneratedRowData topData where
  LocalTarget := PrimitiveAffineEightFrameRow10InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineEightFrameRow10InducedBinding.sourceLocalMap
  sourceLocalMap_surjective :=
    PrimitiveAffineEightFrameRow10InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr
    PrimitiveAffineEightFrameRow10InducedBinding.localTarget_card
  localRepresentation :=
    PrimitiveAffineEightFrameRow10InducedBinding.localRepresentation
  localRepresentation_injective :=
    PrimitiveAffineEightFrameRow10InducedBinding.localRepresentation_injective
  modelRepresentation :=
    PrimitiveAffineEightFrameRow10ModuleRepresentation.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineEightFrameRow10InducedBinding.representation_generator_formula
  moduleRegistry := PrimitiveAffineEightFrameRow10ModuleRegistry.registry

noncomputable def row11Data : GeneratedRowData topData where
  LocalTarget := PrimitiveAffineEightFrameRow11InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineEightFrameRow11InducedBinding.sourceLocalMap
  sourceLocalMap_surjective :=
    PrimitiveAffineEightFrameRow11InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr
    PrimitiveAffineEightFrameRow11InducedBinding.localTarget_card
  localRepresentation :=
    PrimitiveAffineEightFrameRow11InducedBinding.localRepresentation
  localRepresentation_injective :=
    PrimitiveAffineEightFrameRow11InducedBinding.localRepresentation_injective
  modelRepresentation :=
    PrimitiveAffineEightFrameRow11ModuleRepresentation.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineEightFrameRow11InducedBinding.representation_generator_formula
  moduleRegistry := PrimitiveAffineEightFrameRow11ModuleRegistry.registry

noncomputable def row12Data : GeneratedRowData topData where
  LocalTarget := PrimitiveAffineEightFrameRow12InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineEightFrameRow12InducedBinding.sourceLocalMap
  sourceLocalMap_surjective :=
    PrimitiveAffineEightFrameRow12InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr
    PrimitiveAffineEightFrameRow12InducedBinding.localTarget_card
  localRepresentation :=
    PrimitiveAffineEightFrameRow12InducedBinding.localRepresentation
  localRepresentation_injective :=
    PrimitiveAffineEightFrameRow12InducedBinding.localRepresentation_injective
  modelRepresentation :=
    PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineEightFrameRow12InducedBinding.representation_generator_formula
  moduleRegistry := PrimitiveAffineEightFrameRow12ModuleRegistry.registry

noncomputable def row13Data : GeneratedRowData topData where
  LocalTarget := PrimitiveAffineEightFrameRow13InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineEightFrameRow13InducedBinding.sourceLocalMap
  sourceLocalMap_surjective :=
    PrimitiveAffineEightFrameRow13InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr
    PrimitiveAffineEightFrameRow13InducedBinding.localTarget_card
  localRepresentation :=
    PrimitiveAffineEightFrameRow13InducedBinding.localRepresentation
  localRepresentation_injective :=
    PrimitiveAffineEightFrameRow13InducedBinding.localRepresentation_injective
  modelRepresentation :=
    PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineEightFrameRow13InducedBinding.representation_generator_formula
  moduleRegistry := PrimitiveAffineEightFrameRow13ModuleRegistry.registry

end PrimitiveAffineEightFrameTop8GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
