import SymmetricSubgroupAsymptotics.WidthThirtyTwoQuartetNonzeroSource
import SymmetricSubgroupAsymptotics.WidthThirtyTwoZeroOddQuartetSource
import SymmetricSubgroupAsymptotics.ProductQuartetZeroOddCoarseCover
import SymmetricSubgroupAsymptotics.DegreeSixteenActualPairPrimitiveSources

/-! Complete original width-thirty-two source for an actual quartet
system on its sixteen-point top. The paired case is retained before using
the no-pair zero-odd theorem. Every other bound is constructed from the
same original physical frame. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.WidthThirtyTwoCompleteQuartetSource
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathActualOddKernel

def source (p : PreE7PairActionClass 16)
    (F : BinaryPairFrame (preE7PairAction 16 p) (Fin 16))
    (C : ProductBlockFrame F.top.range (Fin 4) Plane)
    [MulAction.IsPretransitive F.top.range (Fin 16)]
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    PreE7RankTailSourceOrYonedaTopData 32
      (preE7SmallPairNonPairAction 16 (by decide) p) := by
  by_cases hp : Nonempty (BinaryPairFrame F.top.range (Fin 8))
  · exact DegreeSixteenActualPairPrimitiveSources.pair_source p F published8 hZmud lit
      (Classical.choice hp)
  by_cases hzero : oddKernel C.quartetLinearImage = ⊥
  · have hT : ¬ IsPGroup 2 F.top.range :=
      F.top_not_isPGroup (preE7PairAction_not_isPGroup 16 p)
    exact WidthThirtyTwoZeroOddQuartetSource.source p F C hzero
      (C.zero_odd_coarse_contains_alternating hzero hT) hp hZmud lit
  · exact WidthThirtyTwoQuartetNonzeroSource.source p F C hzero hZmud lit

end SymmetricSubgroupAsymptotics.WidthThirtyTwoCompleteQuartetSource
