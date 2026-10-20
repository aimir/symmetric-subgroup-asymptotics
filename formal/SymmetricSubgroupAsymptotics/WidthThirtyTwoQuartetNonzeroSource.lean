import SymmetricSubgroupAsymptotics.WidthThirtyTwoQuartetSource
import SymmetricSubgroupAsymptotics.ProductQuartetNonzeroOddQuotientSocles

/-! Complete source in the actual nonzero odd-local-kernel quartet branch.
The top socle, natural module and binary target bounds are all constructed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.WidthThirtyTwoQuartetNonzeroSource
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathActualOddKernel

def source (p : PreE7PairActionClass 16)
    (F : BinaryPairFrame (preE7PairAction 16 p) (Fin 16))
    (C : ProductBlockFrame F.top.range (Fin 4) Plane)
    [MulAction.IsPretransitive F.top.range (Fin 16)]
    (hO : oddKernel C.quartetLinearImage ≠ ⊥)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    PreE7RankTailSourceOrYonedaTopData 32
      (preE7SmallPairNonPairAction 16 (by decide) p) :=
  WidthThirtyTwoQuartetSource.of_nonzero_socle p F C hO
    (fun M _ hQ => C.nonzero_odd_nonbinary_quotientSocle hO M hQ) hZmud lit

end SymmetricSubgroupAsymptotics.WidthThirtyTwoQuartetNonzeroSource
