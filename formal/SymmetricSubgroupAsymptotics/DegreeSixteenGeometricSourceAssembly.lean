import SymmetricSubgroupAsymptotics.DegreeSixteenActualPairPrimitiveSources
import SymmetricSubgroupAsymptotics.WidthThirtyTwoTwoPrimitiveEightSource
import SymmetricSubgroupAsymptotics.SixteenPointMinimalBlockGeometry

/-! Exhaustive actual degree-sixteen top geometry, with the sole
four-quartet source construction left explicit. This is a proved reduction,
not a published classification or a completed sixteen-pair source. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.DegreeSixteenGeometricSourceAssembly
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

/-- The remaining project-owned geometric branch, on the same original
pair action and actual minimal block. -/
abbrev QuartetSource :=
  ∀ (p : PreE7PairActionClass 16)
    (F : BinaryPairFrame (preE7PairAction 16 p) (Fin 16))
    [MulAction.IsPretransitive (preE7PairAction 16 p) (Fin 32)]
    [MulAction.IsPretransitive F.top.range (Fin 16)]
    (point : Fin 16) (D : OriginalMinimalBlock (A := F.top.range) point),
    Nat.card D.Fibre=4 → Nat.card D.Points=4 →
      PreE7RankTailSourceOrYonedaTopData 32
        (preE7SmallPairNonPairAction 16 (by decide) p)

/-- Every other geometric branch is supplied by checked source theorems;
the old overbroad sixteen-point catalogue locator is not used. -/
def representativeSource_of_quartetSource
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (quartet : QuartetSource) : DegreeTwoSixteenPairRepresentativeSource := by
  intro p
  letI : MulAction.IsPretransitive (preE7PairAction 16 p) (Fin 32) :=
    preE7PairAction_pretransitive 16 p
  let F := preE7PairFrame 16 p
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  cases sixteenPointMinimalBlockGeometry F.top.range (Nat.card_fin 16) with
  | primitive hp =>
      exact DegreeSixteenActualPairPrimitiveSources.primitive_source p F
        published16 socle hMN hZmud lit hp
  | pair point D hf hi =>
      let E := (D.binaryPairFrame hf).reindex (Finite.equivFinOfCardEq hi)
      exact DegreeSixteenActualPairPrimitiveSources.pair_source p F published8 hZmud lit E
  | four point D hf hi => exact quartet p F point D hf hi
  | eight point D hf hi =>
      exact WidthThirtyTwoTwoPrimitiveEightSource.source p F point D hf hi
        published8 hZmud lit

def residualSource_of_quartetSource
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (quartet : QuartetSource) : DegreeTwoSixteenPairResidualSource :=
  degreeTwoSixteenPairResidualSource_of_representative
    (representativeSource_of_quartetSource published8 published16 socle hMN hZmud lit quartet)

end SymmetricSubgroupAsymptotics.DegreeSixteenGeometricSourceAssembly
