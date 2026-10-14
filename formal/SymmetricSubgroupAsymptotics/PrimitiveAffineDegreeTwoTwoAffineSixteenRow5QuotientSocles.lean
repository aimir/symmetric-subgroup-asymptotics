import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow19NormalChain
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow5DiagonalTop
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds

/-! Two ambient normal generators for the literal row5 product and all quotient socles. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow5QuotientSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

theorem top_normal_generators
    (N : Subgroup DegreeTwoTwoAffineSixteenInterfaces.row5.top) (hN : N.Normal) :
    ∃ x : Fin 2 → DegreeTwoTwoAffineSixteenInterfaces.row5.top,
      Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective
    PrimitiveAffineDegreeTwoTwoAffineSixteenRow5DiagonalTop.modelEquiv.toMonoidHom
    PrimitiveAffineDegreeTwoTwoAffineSixteenRow5DiagonalTop.modelEquiv.surjective
    (normal_generating_pairs_prod_of_normal_total
      PrimitiveAffineDegreeTwoPairedEightRow19NormalChain.top_normal_total
      DiagonalBinaryPermutationProduct.binary_normal_total) N hN

theorem topSocle
    (N : {N : Subgroup DegreeTwoTwoAffineSixteenInterfaces.row5.top // N.Normal}) :
    SocleNormalGeneratorBound (DegreeTwoTwoAffineSixteenInterfaces.row5.top ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    top_normal_generators N.1

/-- Use the original interface's registry, with no replacement of its state type. -/
noncomputable def family :
    DegreeTwoTwoAffineSixteenInterfaces.row5.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoTwoAffineSixteenInterfaces.row5.normalRegistry topSocle

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow5QuotientSocles
end SymmetricSubgroupAsymptotics

end
