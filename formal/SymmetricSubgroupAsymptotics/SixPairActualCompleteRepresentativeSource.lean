import SymmetricSubgroupAsymptotics.SixPairActualNonbinaryTopSource
import SymmetricSubgroupAsymptotics.SixPairActualTopGeometry
import SymmetricSubgroupAsymptotics.SixPointThreePairNonbinaryQuotientSocles
import SymmetricSubgroupAsymptotics.SixPointTwoTripleNonbinaryQuotientSocles

/-! Every actual transitive nonbinary six-pair action has a complete
source. Primitive tops use the proved primitive source; actual minimal
blocks give three pairs or two triples in every other top. The geometric
socle theorems retain each original normal denominator. No 182-action
source table or per-action certificate is an input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairActualCompleteRepresentativeSource
open Non2UnipotentPrefixFiniteMenu

def source
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (h6 : PublishedPrimitiveDegreeSixClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (p : PreE7PairActionClass 6) :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) := by
  letI : MulAction.IsPretransitive (preE7PairAction 6 p) (Fin 12) :=
    preE7PairAction_pretransitive 6 p
  let F := preE7PairFrame 6 p
  cases SixPairActualTopGeometry.source_or_imprimitive socle catalogue h6 hZmud p F with
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
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (h6 : PublishedPrimitiveDegreeSixClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    DegreeTwoSixPairRepresentativeSource := source socle catalogue h6 hZmud lit

end SymmetricSubgroupAsymptotics.SixPairActualCompleteRepresentativeSource
