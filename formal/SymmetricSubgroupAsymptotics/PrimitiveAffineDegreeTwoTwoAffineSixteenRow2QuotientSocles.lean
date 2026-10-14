import SymmetricSubgroupAsymptotics.BinaryDiagonalSwapAffine
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow2SwapTop
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds

/-! All actual quotient socles for row2, through its diagonal translation
kernel and the already checked local affine normal chain. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow2QuotientSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoPairedEightAffineTops

theorem model_normal_generators :
    ∀ N : Subgroup PrimitiveAffineDegreeTwoTwoAffineSixteenRow2SwapTop.Model, N.Normal →
      ∃ x : Fin 2 → PrimitiveAffineDegreeTwoTwoAffineSixteenRow2SwapTop.Model,
        Subgroup.normalClosure (Set.range x) = N :=
  BinaryDiagonalSwap.affine_normal_generating_tuples Row18.linearGroup
    Row18.irreducible (by decide)
    (DiagonalBinaryPermutationProduct.normal_generating_pairs_of_equiv
      Row18.normalChain
      (Row18.modelEquiv.prodCongr (MulEquiv.refl BinaryDiagonalSwap.Binary)))

theorem top_normal_generators
    (N : Subgroup DegreeTwoTwoAffineSixteenInterfaces.row2.top) (hN : N.Normal) :
    ∃ x : Fin 2 → DegreeTwoTwoAffineSixteenInterfaces.row2.top,
      Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective
    PrimitiveAffineDegreeTwoTwoAffineSixteenRow2SwapTop.modelEquiv.toMonoidHom
    PrimitiveAffineDegreeTwoTwoAffineSixteenRow2SwapTop.modelEquiv.surjective
    model_normal_generators N hN

theorem topSocle
    (N : {N : Subgroup DegreeTwoTwoAffineSixteenInterfaces.row2.top // N.Normal}) :
    SocleNormalGeneratorBound (DegreeTwoTwoAffineSixteenInterfaces.row2.top ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    top_normal_generators N.1

noncomputable def family :
    DegreeTwoTwoAffineSixteenInterfaces.row2.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoTwoAffineSixteenInterfaces.row2.normalRegistry topSocle

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow2QuotientSocles
end SymmetricSubgroupAsymptotics

end
