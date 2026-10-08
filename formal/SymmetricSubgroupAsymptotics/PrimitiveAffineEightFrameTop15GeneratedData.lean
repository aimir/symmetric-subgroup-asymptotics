import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameGeneratedLocalNormalTable
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop15TopRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistry

/-!
# Shared generated data for eight-frame top 15

Rows 24 share one literal transitive top and one point stabilizer.
Only their local quotient maps and binary modules remain row-varying.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineEightFrameTop15GeneratedData

abbrev Source := PrimitiveAffineEightFrameTop15TopCertificate.Source
local instance sourceGroup : Group Source :=
  PrimitiveAffineEightFrameTop15TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range PrimitiveAffineEightFrameTop15TopCertificate.generators)

abbrev sourceStabilizer : Subgroup Source :=
  PrimitiveAffineEightFrameRow24InducedBinding.sourceStabilizer

instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable (PrimitiveAffineEightFrameRow24InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineEightFrameRow24InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineEightFrameTop15TopCertificate.originalEquiv x :
        LiteralAction) : Equiv.Perm (Fin 8))) (0 : Fin 8) = 0) := by
  intro x
  change PrimitiveAffineEightFrameRow24InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineEightFrameTop15TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineEightFrameRow24InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 8) :=
  GeneratedTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineEightFrameTop15TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv := PrimitiveAffineEightFrameTop15TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction PrimitiveAffineEightFrameTop15TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 5
  ambient := PrimitiveAffineEightFrameTop15TopCertificate.ambient
  ambient_full := PrimitiveAffineEightFrameTop15TopCertificate.ambient_full
  representative := PrimitiveAffineEightFrameRow24InducedBinding.representative
  representative_factor := PrimitiveAffineEightFrameRow24InducedBinding.representative_factor
  next := PrimitiveAffineEightFrameRow24InducedBinding.next
  twist := PrimitiveAffineEightFrameRow24InducedBinding.twist
  representative_mul_generator := PrimitiveAffineEightFrameRow24InducedBinding.representative_mul_generator
  classCount := 13
  conjugacyRepresentative := PrimitiveAffineEightFrameTop15TopCertificate.representative
  conjugacyCover := PrimitiveAffineEightFrameTop15TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 8
  NormalGeneratorIndex := Fin 6
  stateGenerators := PrimitiveAffineEightFrameTop15NormalCertificate.stateGenerators
  topRegistry := PrimitiveAffineEightFrameTop15TopRegistry.registry

noncomputable def row24Data : GeneratedRowData topData where
  LocalTarget := PrimitiveAffineEightFrameRow24InducedBinding.LocalTarget
  sourceLocalMap := PrimitiveAffineEightFrameRow24InducedBinding.sourceLocalMap
  sourceLocalMap_surjective := PrimitiveAffineEightFrameRow24InducedBinding.sourceLocalMap_surjective
  local_card := Or.inr PrimitiveAffineEightFrameRow24InducedBinding.localTarget_card
  localRepresentation := PrimitiveAffineEightFrameRow24InducedBinding.localRepresentation
  localRepresentation_injective := PrimitiveAffineEightFrameRow24InducedBinding.localRepresentation_injective
  modelRepresentation := PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
  modelRepresentation_generator_formula :=
    PrimitiveAffineEightFrameRow24InducedBinding.representation_generator_formula
  moduleRegistry := PrimitiveAffineEightFrameRow24ModuleRegistry.registry

end PrimitiveAffineEightFrameTop15GeneratedData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
