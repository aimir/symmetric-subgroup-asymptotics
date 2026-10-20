import SymmetricSubgroupAsymptotics.WidthThirtyTwoOriginalPairSource
import SymmetricSubgroupAsymptotics.QuartetBlockNaturalUniformEight
import SymmetricSubgroupAsymptotics.QuartetOddOriginalBinaryQuotientOrder
import SymmetricSubgroupAsymptotics.ProductBlockFrameOrderBound
import SymmetricSubgroupAsymptotics.ProductBlockFrameFibreReindex
import SymmetricSubgroupAsymptotics.PairedEightTopCostNumerics

/-! Original width-thirty-two quartet sources. The natural-module and
binary-target estimates are derived from the actual block action. The
nonbinary top socle input is isolated for the geometric dispatch. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.WidthThirtyTwoQuartetSource
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathActualOddKernel

variable (p : PreE7PairActionClass 16)
  (F : BinaryPairFrame (preE7PairAction 16 p) (Fin 16))
  (C : ProductBlockFrame F.top.range (Fin 4) Plane)
  [MulAction.IsPretransitive F.top.range (Fin 16)]

include C in
theorem natural_uniform_eight :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 16)) 8 := by
  let e : Fin 4 ≃ Plane :=
    (Finite.equivFinOfCardEq (by simp [Plane, Nat.card_eq_fintype_card])).symm
  exact QuartetBlockNaturalUniformEight.uniform (C.reindexFibre e)

/-- The same original action and every original normal denominator are
retained in both parts of the split estimate. -/
def of_nonzero_socle
    (hO : oddKernel C.quartetLinearImage ≠ ⊥)
    (hsocle : ∀ (M : Subgroup F.top.range) [M.Normal],
      ¬ IsPGroup 2 (F.top.range ⧸ M) →
        SocleNormalGeneratorBound (F.top.range ⧸ M) 2)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    PreE7RankTailSourceOrYonedaTopData 32
      (preE7SmallPairNonPairAction 16 (by decide) p) := by
  have ht : Nat.card F.top.range ≤ 2 ^ 32 :=
    C.quartet_order_le (Nat.card_fin 4) (by simp [Plane, Nat.card_eq_fintype_card])
  apply WidthThirtyTwoOriginalPairSource.of_split_socle p F ht (39 / 10)
    (by norm_num [halfDegree, preE7CharacterRho])
    (natural_uniform_eight p F C) hsocle
    (fun N _ hQ => F.binary_quotient_card_le_fifteen C hO N hQ)
    hZmud lit
  · norm_num
    linarith [PairedEightTopCostNumerics.ordinary_le]
  · norm_num

end SymmetricSubgroupAsymptotics.WidthThirtyTwoQuartetSource
