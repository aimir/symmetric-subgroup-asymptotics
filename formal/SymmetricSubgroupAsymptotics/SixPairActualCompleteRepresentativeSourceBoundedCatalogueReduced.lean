import SymmetricSubgroupAsymptotics.SixPairActualCompleteRepresentativeSource
import SymmetricSubgroupAsymptotics.PrimitiveSixTwelveNormalConsumerFacts
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.SixPairActualTopGeometryBoundedCatalogueReduced

/-! Isolated actual degree6/12 normal-consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics.SixPairActualCompleteRepresentativeSource

namespace BoundedCatalogueReduced

open Non2UnipotentPrefixFiniteMenu

def source
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts)
    (h6 : PublishedPrimitiveDegreeSixClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (p : PreE7PairActionClass 6) :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) := by
  letI : MulAction.IsPretransitive (preE7PairAction 6 p) (Fin 12) :=
    preE7PairAction_pretransitive 6 p
  let F := preE7PairFrame 6 p
  cases _root_.SymmetricSubgroupAsymptotics.SixPairActualTopGeometry.BoundedCatalogueReduced.source_or_imprimitive socle catalogue h6 hZmud p F with
  | inl h => exact h
  | inr geometry =>
      letI : MulAction.IsPretransitive F.top.range (Fin 6) := F.top_pretransitive
      apply SixPairActualNonbinaryTopSource.source p F _ hZmud lit
      intro M hM hnonbinary
      cases geometry with
      | threePairs E =>
          let B : BinaryPairFrame F.top.range (Fin 3) :=
            { frame := E.frame, top := E.top, intertwine := E.intertwine }
          exact SixPointThreePairNonbinaryQuotientSocles.quotient B M hnonbinary
      | twoTriples E =>
          exact SixPointTwoTripleNonbinaryQuotientSocles.quotient F.top.range E M hnonbinary

def representativeSource
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts)
    (h6 : PublishedPrimitiveDegreeSixClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    DegreeTwoSixPairRepresentativeSource := _root_.SymmetricSubgroupAsymptotics.SixPairActualCompleteRepresentativeSource.BoundedCatalogueReduced.source socle catalogue h6 hZmud lit

end BoundedCatalogueReduced

end SymmetricSubgroupAsymptotics.SixPairActualCompleteRepresentativeSource

