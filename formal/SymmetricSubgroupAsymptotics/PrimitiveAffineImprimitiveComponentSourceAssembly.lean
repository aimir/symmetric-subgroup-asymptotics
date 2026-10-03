import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveCapacityExhaustion

/-!
# Assemble the imprimitive affine component source

The generic actual-wreath calculation already supplies a `ComponentSource`
outside the finite exceptional affine cells.  This file isolates the exact
remaining construction: a consumer only for a witnessed value of
`ImprimitiveAffineCapacityException`.  It then assembles the full component
source by case analysis on the proved numerical exhaustion.

The exceptional consumer is a temporary construction boundary, not a
literature input.  It is deliberately stated on the literal original block,
the literal affine profile, and the proof of the exact exceptional cell, so
that the finite affine-frame arguments cannot silently replace the original
action or its source.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- The exact finite affine-frame obligation left by
`ComponentSource.capacityExhaustion`.  This is project-owned construction
data and is not an admissible final assumption of `T1`. -/
structure PreE7PrimitiveAffineExceptionalCellConsumerData : Type 1 where
  source : ∀ w (U : PreE7NonPairActionClass w), 5 ≤ w →
    (basePoint : Fin w) →
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint) →
    (P : PrimitiveAffineProfile block.Component block.Fibre) →
    ImprimitiveAffineCapacityException
      (Nat.card block.Fibre) (Nat.card block.Points) →
    PreE7RankTailSourceOrYonedaTopData w U

/-- The proved generic capacity exhaustion plus the literal exceptional-cell
consumer gives the complete construction-facing affine component source. -/
noncomputable def preE7PrimitiveAffineImprimitiveComponentSourceData
    (D : PublishedPrimitiveAffineSmallCatalogueData)
    (hcomp : PrimitiveCompositionLengthInput)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (exceptional : PreE7PrimitiveAffineExceptionalCellConsumerData) :
    PreE7PrimitiveAffineImprimitiveComponentSourceData
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm where
  source := by
    intro w U hw basePoint block P
    exact match ComponentSource.capacityExhaustion
        hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P D hcomp with
      | .inl source => .inl source
      | .inr h => .inr (exceptional.source w U hw basePoint block P h.down)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
