import SymmetricSubgroupAsymptotics.WidthThirtyTwoQuartetSource
import SymmetricSubgroupAsymptotics.ProductQuartetZeroOddQuotientBounds
import SymmetricSubgroupAsymptotics.QuartetZeroOddOriginalBinaryQuotientOrder

/-! Complete original width-thirty-two source for a zero-odd quartet top
with honest no-pair geometry. All original quotient estimates are derived
from the physical quartet frame, including the separate binary target
order bound. No twenty-nine-row exhaustion premise is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.WidthThirtyTwoZeroOddQuartetSource
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathActualOddKernel

/-- The paired outcome is handled by the independent actual paired-top
source; this theorem covers its actual geometric complement. -/
def source
    (p : PreE7PairActionClass 16)
    (F : BinaryPairFrame (preE7PairAction 16 p) (Fin 16))
    (C : ProductBlockFrame F.top.range (Fin 4) Plane)
    [MulAction.IsPretransitive F.top.range (Fin 16)]
    (hzero : oddKernel C.quartetLinearImage = ⊥)
    (heven : alternatingGroup (Fin 4) ≤ C.top.range)
    (hNoPair : ¬ Nonempty (BinaryPairFrame F.top.range (Fin 8)))
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    PreE7RankTailSourceOrYonedaTopData 32
      (preE7SmallPairNonPairAction 16 (by decide) p) := by
  have ht : Nat.card F.top.range ≤ 2 ^ 32 :=
    C.quartet_order_le (Nat.card_fin 4) (by simp [Plane, Nat.card_eq_fintype_card])
  apply WidthThirtyTwoOriginalPairSource.of_split_socle p F ht (39 / 10)
    (by norm_num [halfDegree, preE7CharacterRho])
    (WidthThirtyTwoQuartetSource.natural_uniform_eight p F C)
    (fun M _ hQ => C.zeroOdd_nonbinary_quotient_socle_two hzero heven hNoPair M hQ)
    (fun N _ hQ => (F.zeroOdd_binary_quotient_card_le_eleven C hzero heven hNoPair N hQ).trans
      (by norm_num : (2 : ℕ)^11 ≤ 2^15))
    hZmud lit
  · norm_num
    linarith [PairedEightTopCostNumerics.ordinary_le]
  · norm_num

end SymmetricSubgroupAsymptotics.WidthThirtyTwoZeroOddQuartetSource
