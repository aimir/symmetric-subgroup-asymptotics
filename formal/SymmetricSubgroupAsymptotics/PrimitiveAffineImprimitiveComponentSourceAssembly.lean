import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveCapacityExhaustion
import SymmetricSubgroupAsymptotics.PrimitiveAffineTranslationLayerSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeCyclicComponent

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

/-- A numerical-capacity exception after removing the cells closed directly
by the faithful translation-layer comparator. -/
structure ImprimitiveAffineResidualCapacityException
    (r s componentOrder : ℕ) : Prop where
  toCapacityException : ImprimitiveAffineCapacityException r s
  not_directTranslation :
    ¬ ((r = 3 ∧ s = 8) ∨ (r = 5 ∧ s = 4))
  not_degreeThreeCyclic :
    ¬ (r = 3 ∧ (s = 3 ∨ s = 4 ∨ s = 12 ∨ s = 18) ∧
      componentOrder ∣ 3)

/-- The exact residual affine-frame obligation left by the numerical
capacity exhaustion and the direct translation stops. This is project-owned
construction data and is not an admissible final assumption of T1. -/
structure PreE7PrimitiveAffineExceptionalCellConsumerData : Type 1 where
  residualSource : ∀ w (U : PreE7NonPairActionClass w), 5 ≤ w →
    (basePoint : Fin w) →
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint) →
    (P : PrimitiveAffineProfile block.Component block.Fibre) →
    ImprimitiveAffineResidualCapacityException
      (Nat.card block.Fibre) (Nat.card block.Points)
        (Nat.card block.Component) →
    PreE7RankTailSourceOrYonedaTopData w U

namespace PreE7PrimitiveAffineExceptionalCellConsumerData

/-- Consume a full numerical exception.  The two direct translation cells
are discharged here, before reaching the smaller project-owned residual
menu. -/
noncomputable def consume
    (D : PreE7PrimitiveAffineExceptionalCellConsumerData)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    {w : ℕ} (U : PreE7NonPairActionClass w) (hw : 5 ≤ w)
    (basePoint : Fin w)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (h : ImprimitiveAffineCapacityException
      (Nat.card block.Fibre) (Nat.card block.Points)) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P ⊕
      PreE7RankTailSourceOrYonedaTopData w U := by
  by_cases h38 :
      Nat.card block.Fibre = 3 ∧ Nat.card block.Points = 8
  · letI : Nontrivial block.Fibre :=
      Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
    exact .inr (degreeThreeEightTranslationSource block P
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm h38.1 h38.2
    )
  by_cases h54 :
      Nat.card block.Fibre = 5 ∧ Nat.card block.Points = 4
  · letI : Nontrivial block.Fibre :=
      Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
    exact .inr (degreeFiveFourTranslationSource block P
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm h54.1 h54.2
    )
  by_cases h3cyclic :
      Nat.card block.Fibre = 3 ∧
        (Nat.card block.Points = 3 ∨ Nat.card block.Points = 4 ∨
          Nat.card block.Points = 12 ∨ Nat.card block.Points = 18) ∧
        Nat.card block.Component ∣ 3
  · rcases h3cyclic with ⟨hr, hs, hcomponent⟩
    by_cases hs3 : Nat.card block.Points = 3
    · exact .inl (ComponentSource.of_degreeThree_threeBlocks_cyclic hTraceyHalf
        hTraceyLog hTraceyRefined hTraceyPerm block P hr hs3 hcomponent)
    by_cases hs4 : Nat.card block.Points = 4
    · exact .inl (ComponentSource.of_degreeThree_fourBlocks_cyclic hTraceyHalf
        hTraceyLog hTraceyRefined hTraceyPerm block P hr hs4 hcomponent)
    by_cases hs12 : Nat.card block.Points = 12
    · exact .inl (ComponentSource.of_degreeThree_twelveBlocks_cyclic hTraceyHalf
        hTraceyLog hTraceyRefined hTraceyPerm block P hr hs12 hcomponent)
    · have hs18 : Nat.card block.Points = 18 :=
        hs.resolve_left hs3 |>.resolve_left hs4 |>.resolve_left hs12
      exact .inl (ComponentSource.of_degreeThree_eighteenBlocks_cyclic hTraceyHalf
        hTraceyLog hTraceyRefined hTraceyPerm block P hr hs18 hcomponent)
  · exact .inr (D.residualSource w U hw basePoint block P
      ⟨h, by simpa only [not_or] using And.intro h38 h54, h3cyclic⟩)

end PreE7PrimitiveAffineExceptionalCellConsumerData

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
      | .inr h => exceptional.consume hTraceyHalf hTraceyLog hTraceyRefined
          hTraceyPerm U hw basePoint block P h.down

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
