import SymmetricSubgroupAsymptotics.WidthThirtyTwoOriginalPairSource
import SymmetricSubgroupAsymptotics.TwoPrimitiveEightBlockNaturalUniform
import SymmetricSubgroupAsymptotics.TwoPrimitiveEightBlockQuotientSocles
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockProductFrame
import SymmetricSubgroupAsymptotics.ProductBlockFrameOrderBound
import SymmetricSubgroupAsymptotics.PairedEightTopCostNumerics

/-! Complete original width-thirty-two source when its actual sixteen-point
top has two primitive eight-point blocks. All seven local primitive types
are covered through the bare degree-eight classification. The original
binary kernel and every original normal denominator are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.WidthThirtyTwoTwoPrimitiveEightSource
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

/-- The actual local component supplies both the three-slot top bound and
the four-slot natural-module bound; neither is assumed by the source. -/
def source
    (p : PreE7PairActionClass 16)
    (F : BinaryPairFrame (preE7PairAction 16 p) (Fin 16))
    [MulAction.IsPretransitive (preE7PairAction 16 p) (Fin 32)]
    [MulAction.IsPretransitive F.top.range (Fin 16)]
    (point : Fin 16) (D : OriginalMinimalBlock (A := F.top.range) point)
    (hf : Nat.card D.Fibre = 8) (hi : Nat.card D.Points = 2)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    PreE7RankTailSourceOrYonedaTopData 32
      (preE7SmallPairNonPairAction 16 (by decide) p) := by
  let C := D.productFrame (Finite.equivFinOfCardEq hi) (Finite.equivFinOfCardEq hf)
  have ht : Nat.card F.top.range ≤ 2 ^ 32 :=
    C.two_eight_order_le (Nat.card_fin 2) (Nat.card_fin 8)
  apply WidthThirtyTwoOriginalPairSource.of_uniform_socle p F ht (39 / 10)
    (by norm_num [halfDegree, preE7CharacterRho])
    (D.twoPrimitiveEight_natural_uniform_four published8 hf hi)
    (fun M _ => D.twoPrimitiveEight_quotient_socle_three published8 hf hi M)
    hZmud lit
  norm_num
  linarith [PairedEightTopCostNumerics.ordinary_le]

end SymmetricSubgroupAsymptotics.WidthThirtyTwoTwoPrimitiveEightSource
