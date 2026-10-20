import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenDiagonalTops
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow20AffineSocleClosure
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds

/-! The actual row11 top is the checked local Top20 times the binary block swap. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow11QuotientSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

theorem top_normal_generators
    (N : Subgroup DegreeTwoTwoAffineSixteenInterfaces.row11.top) (hN : N.Normal) :
    ∃ x : Fin 2 → DegreeTwoTwoAffineSixteenInterfaces.row11.top,
      Subgroup.normalClosure (Set.range x) = N :=
  DiagonalBinaryPermutationProduct.normal_generating_pairs_of_equiv
    PrimitiveAffineDegreeTwoPairedEightAffineTops.Row20.normalChain
    PrimitiveAffineDegreeTwoTwoAffineSixteenDiagonalTops.Row11.modelEquiv N hN

theorem topSocle
    (N : {N : Subgroup DegreeTwoTwoAffineSixteenInterfaces.row11.top // N.Normal}) :
    SocleNormalGeneratorBound (DegreeTwoTwoAffineSixteenInterfaces.row11.top ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    top_normal_generators N.1

/-- Retain the literal interface's original normal-state registry. -/
noncomputable def family :
    DegreeTwoTwoAffineSixteenInterfaces.row11.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoTwoAffineSixteenInterfaces.row11.normalRegistry topSocle

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow11QuotientSocles
end SymmetricSubgroupAsymptotics

end
