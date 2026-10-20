import SymmetricSubgroupAsymptotics.BinaryDiagonalSwapAffine
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow20AffineSocleClosure
import SymmetricSubgroupAsymptotics.DiagonalBinaryPermutationProduct
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds

/-! Original row13 quotient socles from the shared diagonal kernel cover. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow13QuotientSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoPairedEightAffineTops

theorem model_normal_generators :
    ∀ N : Subgroup PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop.Model, N.Normal →
      ∃ x : Fin 2 → PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop.Model,
        Subgroup.normalClosure (Set.range x) = N :=
  BinaryDiagonalSwap.affine_normal_generating_tuples Row20.linearGroup
    Row20.irreducible (by decide)
    (DiagonalBinaryPermutationProduct.normal_generating_pairs_of_equiv
      Row20.normalChain
      (Row20.modelEquiv.prodCongr (MulEquiv.refl BinaryDiagonalSwap.Binary)))

theorem top_normal_generators
    (N : Subgroup DegreeTwoTwoAffineSixteenInterfaces.row13.top) (hN : N.Normal) :
    ∃ x : Fin 2 → DegreeTwoTwoAffineSixteenInterfaces.row13.top,
      Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective
    PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop.modelEquiv.toMonoidHom
    PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop.modelEquiv.surjective
    model_normal_generators N hN

theorem topSocle
    (N : {N : Subgroup DegreeTwoTwoAffineSixteenInterfaces.row13.top // N.Normal}) :
    SocleNormalGeneratorBound (DegreeTwoTwoAffineSixteenInterfaces.row13.top ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    top_normal_generators N.1

noncomputable def family :
    DegreeTwoTwoAffineSixteenInterfaces.row13.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoTwoAffineSixteenInterfaces.row13.normalRegistry topSocle

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow13QuotientSocles
end SymmetricSubgroupAsymptotics

end
