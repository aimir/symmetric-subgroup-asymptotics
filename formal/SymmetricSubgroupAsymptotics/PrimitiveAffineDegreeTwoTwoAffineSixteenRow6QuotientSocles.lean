import SymmetricSubgroupAsymptotics.BinaryDiagonalSwapAffine
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow6SwapTop
import SymmetricSubgroupAsymptotics.DiagonalBinaryPermutationProduct
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds

/-! Original row6 quotient socles from the shared diagonal kernel cover. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow6QuotientSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

theorem local_product_normal_generators :
    ∀ N : Subgroup
        (AffineModel.Aff PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.linearGroup ×
          BinaryDiagonalSwap.Binary), N.Normal →
      ∃ x : Fin 2 →
          AffineModel.Aff PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.linearGroup ×
            BinaryDiagonalSwap.Binary,
        Subgroup.normalClosure (Set.range x) = N := by
  let e := PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.modelEquiv.prodCongr
    (MulEquiv.refl BinaryDiagonalSwap.Binary)
  exact normal_generating_tuples_of_surjective e.toMonoidHom e.surjective
    (normal_generating_pairs_prod_of_normal_total
      PrimitiveAffineDegreeTwoPairedEightRow19NormalChain.top_normal_total
      DiagonalBinaryPermutationProduct.binary_normal_total)

theorem model_normal_generators :
    ∀ N : Subgroup PrimitiveAffineDegreeTwoTwoAffineSixteenRow6SwapTop.Model, N.Normal →
      ∃ x : Fin 2 → PrimitiveAffineDegreeTwoTwoAffineSixteenRow6SwapTop.Model,
        Subgroup.normalClosure (Set.range x) = N :=
  BinaryDiagonalSwap.affine_normal_generating_tuples
    PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.linearGroup
    PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.irreducible (by decide)
    local_product_normal_generators

theorem top_normal_generators
    (N : Subgroup DegreeTwoTwoAffineSixteenInterfaces.row6.top) (hN : N.Normal) :
    ∃ x : Fin 2 → DegreeTwoTwoAffineSixteenInterfaces.row6.top,
      Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective
    PrimitiveAffineDegreeTwoTwoAffineSixteenRow6SwapTop.modelEquiv.toMonoidHom
    PrimitiveAffineDegreeTwoTwoAffineSixteenRow6SwapTop.modelEquiv.surjective
    model_normal_generators N hN

theorem topSocle
    (N : {N : Subgroup DegreeTwoTwoAffineSixteenInterfaces.row6.top // N.Normal}) :
    SocleNormalGeneratorBound (DegreeTwoTwoAffineSixteenInterfaces.row6.top ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    top_normal_generators N.1

noncomputable def family :
    DegreeTwoTwoAffineSixteenInterfaces.row6.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoTwoAffineSixteenInterfaces.row6.normalRegistry topSocle

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow6QuotientSocles
end SymmetricSubgroupAsymptotics

end
