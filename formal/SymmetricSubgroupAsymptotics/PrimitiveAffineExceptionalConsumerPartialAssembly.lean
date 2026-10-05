import SymmetricSubgroupAsymptotics.PrimitiveAffineExceptionalKnownDegreeSources

/-!
# Assemble the affine exceptional consumer from the three low-degree lanes

Degrees five, eight, nine, and sixteen have unconditional source
constructors.  This dispatcher proves that only the independent degree-two,
degree-three, and degree-four source functions remain to build the complete
exceptional-cell consumer.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- Assemble the full residual-cell consumer after supplying the three
independent low-degree source constructions. -/
noncomputable def
    preE7PrimitiveAffineExceptionalCellConsumerData_of_lowDegreeSources
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (published : PublishedPrimitiveAffineSmallCatalogueData)
    (degreeTwo : ∀ {w : ℕ} (U : PreE7NonPairActionClass w) (_hw : 5 ≤ w)
      (basePoint : Fin w)
      (block : OriginalMinimalBlock
        (A := preE7NonPairAction w U) basePoint)
      (P : PrimitiveAffineProfile block.Component block.Fibre),
      ImprimitiveAffineResidualCapacityException
          (Nat.card block.Fibre) (Nat.card block.Points)
          (Nat.card block.Component) →
      Nat.card block.Fibre = 2 →
      PreE7RankTailSourceOrYonedaTopData w U)
    (degreeThree : ∀ {w : ℕ} (U : PreE7NonPairActionClass w) (_hw : 5 ≤ w)
      (basePoint : Fin w)
      (block : OriginalMinimalBlock
        (A := preE7NonPairAction w U) basePoint)
      (P : PrimitiveAffineProfile block.Component block.Fibre),
      ImprimitiveAffineResidualCapacityException
          (Nat.card block.Fibre) (Nat.card block.Points)
          (Nat.card block.Component) →
      Nat.card block.Fibre = 3 →
      PreE7RankTailSourceOrYonedaTopData w U)
    (degreeFour : ∀ {w : ℕ} (U : PreE7NonPairActionClass w) (_hw : 5 ≤ w)
      (basePoint : Fin w)
      (block : OriginalMinimalBlock
        (A := preE7NonPairAction w U) basePoint)
      (P : PrimitiveAffineProfile block.Component block.Fibre),
      ImprimitiveAffineResidualCapacityException
          (Nat.card block.Fibre) (Nat.card block.Points)
          (Nat.card block.Component) →
      Nat.card block.Fibre = 4 →
      PreE7RankTailSourceOrYonedaTopData w U) :
    PreE7PrimitiveAffineExceptionalCellConsumerData where
  residualSource := by
    intro w U hw basePoint block P h
    refine Classical.choice ?_
    cases h.toCapacityException with
    | degreeTwo hr hs =>
        exact ⟨degreeTwo U hw basePoint block P h hr⟩
    | degreeThree hr hs =>
        exact ⟨degreeThree U hw basePoint block P h hr⟩
    | degreeFour hr hs =>
        exact ⟨degreeFour U hw basePoint block P h hr⟩
    | degreeFive hr hs =>
        rcases hs with hs | hs | hs
        · exact ⟨degreeFiveResidualCharacterSource hZmud lit hTraceyHalf
            hTraceyPerm block P hr (Or.inl hs)⟩
        · exact ⟨degreeFiveResidualCharacterSource hZmud lit hTraceyHalf
            hTraceyPerm block P hr (Or.inr hs)⟩
        · exact False.elim (h.not_directTranslation (Or.inr ⟨hr, hs⟩))
    | degreeEight hr hs =>
        exact ⟨degreeEightOrSixteenResidualSource hZmud lit hgen hClifford
          hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hSimpleGen
          published block P h.toCapacityException (Or.inl hr)⟩
    | degreeNine hr hs =>
        exact ⟨degreeNineResidualCharacterSource hClifford hTraceyHalf
          hTraceyPerm hgen hZmud lit block P hr hs⟩
    | degreeSixteen hr hs =>
        exact ⟨degreeEightOrSixteenResidualSource hZmud lit hgen hClifford
          hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hSimpleGen
          published block P h.toCapacityException (Or.inr hr)⟩

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
