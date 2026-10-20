import SymmetricSubgroupAsymptotics.SixPairActualTopGeometry
import SymmetricSubgroupAsymptotics.PrimitiveSixTwelveNormalConsumerFacts
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.SixPairPrimitiveRepresentativeSourceBoundedCatalogueReduced

/-! Isolated actual degree6/12 normal-consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

open scoped Classical

namespace SymmetricSubgroupAsymptotics.SixPairActualTopGeometry

namespace BoundedCatalogueReduced

open Non2UnipotentPrefixFiniteMenu

def source_or_imprimitive
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts)
    (h6 : PublishedPrimitiveDegreeSixClassification) (hZmud : ZmudFaithfulCharacterTupleInput)
    (p : PreE7PairActionClass 6)
    (F : BinaryPairFrame (preE7PairAction 6 p) (Fin 6))
    [MulAction.IsPretransitive (preE7PairAction 6 p) (Fin 12)] :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) ⊕
      ImprimitiveGeometry F.top.range := by
  letI : MulAction.IsPretransitive F.top.range (Fin 6) := F.top_pretransitive
  by_cases hp : MulAction.IsPreprimitive F.top.range (Fin 6)
  · letI := hp
    exact .inl (_root_.SymmetricSubgroupAsymptotics.SixPairPrimitiveRepresentativeSource.BoundedCatalogueReduced.source socle catalogue h6 hZmud p F)
  · exact .inr (imprimitiveGeometry F.top.range hp)

end BoundedCatalogueReduced

end SymmetricSubgroupAsymptotics.SixPairActualTopGeometry

