import SymmetricSubgroupAsymptotics.SixPairActualTopGeometry
import SymmetricSubgroupAsymptotics.SixPairPrimitiveRepresentativeSourceDirectSix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixPairActualTopGeometry.DirectSix
open Non2UnipotentPrefixFiniteMenu

def source_or_imprimitive
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) (hZmud : ZmudFaithfulCharacterTupleInput)
    (p : PreE7PairActionClass 6)
    (F : BinaryPairFrame (preE7PairAction 6 p) (Fin 6))
    [MulAction.IsPretransitive (preE7PairAction 6 p) (Fin 12)] :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) ⊕
      ImprimitiveGeometry F.top.range := by
  letI : MulAction.IsPretransitive F.top.range (Fin 6) := F.top_pretransitive
  by_cases hp : MulAction.IsPreprimitive F.top.range (Fin 6)
  · letI := hp
    exact .inl (SixPairPrimitiveRepresentativeSource.DirectSix.source hindex hZmud p F)
  · exact .inr (imprimitiveGeometry F.top.range hp)


end SymmetricSubgroupAsymptotics.SixPairActualTopGeometry.DirectSix
