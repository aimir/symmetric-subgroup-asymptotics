import SymmetricSubgroupAsymptotics.SixPairActualCompleteRepresentativeSource
import SymmetricSubgroupAsymptotics.SixPairActualTopGeometryDirectSix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixPairActualCompleteRepresentativeSource.DirectSix
open Non2UnipotentPrefixFiniteMenu

def source
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (p : PreE7PairActionClass 6) :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) := by
  letI : MulAction.IsPretransitive (preE7PairAction 6 p) (Fin 12) :=
    preE7PairAction_pretransitive 6 p
  let F := preE7PairFrame 6 p
  cases SixPairActualTopGeometry.DirectSix.source_or_imprimitive hindex hZmud p F with
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
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    DegreeTwoSixPairRepresentativeSource := source hindex hZmud lit


end SymmetricSubgroupAsymptotics.SixPairActualCompleteRepresentativeSource.DirectSix
