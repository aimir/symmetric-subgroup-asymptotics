import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenDiagonalTops
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightAffineSocles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds

/-! The actual row1 top is the checked local Top18 times the binary block swap. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow1QuotientSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

theorem top_normal_generators
    (N : Subgroup DegreeTwoTwoAffineSixteenInterfaces.row1.top) (hN : N.Normal) :
    ∃ x : Fin 2 → DegreeTwoTwoAffineSixteenInterfaces.row1.top,
      Subgroup.normalClosure (Set.range x) = N :=
  DiagonalBinaryPermutationProduct.normal_generating_pairs_of_equiv
    PrimitiveAffineDegreeTwoPairedEightAffineTops.Row18.normalChain
    PrimitiveAffineDegreeTwoTwoAffineSixteenDiagonalTops.Row1.modelEquiv N hN

theorem topSocle
    (N : {N : Subgroup DegreeTwoTwoAffineSixteenInterfaces.row1.top // N.Normal}) :
    SocleNormalGeneratorBound (DegreeTwoTwoAffineSixteenInterfaces.row1.top ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    top_normal_generators N.1

/-- Retain the literal interface's original normal-state registry. -/
noncomputable def family :
    DegreeTwoTwoAffineSixteenInterfaces.row1.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoTwoAffineSixteenInterfaces.row1.normalRegistry topSocle

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow1QuotientSocles
end SymmetricSubgroupAsymptotics

end
