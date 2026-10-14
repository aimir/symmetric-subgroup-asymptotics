import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow14TwistedTop
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds

/-! Every quotient of the exact original two-affine row14 has socle width2. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow14QuotientSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

theorem top_normal_generators
    (N : Subgroup DegreeTwoTwoAffineSixteenInterfaces.row14.top) (hN : N.Normal) :
    ∃ x : Fin 2 → DegreeTwoTwoAffineSixteenInterfaces.row14.top,
      Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective
    PrimitiveAffineDegreeTwoTwoAffineSixteenRow14TwistedTop.modelEquiv.toMonoidHom
    PrimitiveAffineDegreeTwoTwoAffineSixteenRow14TwistedTop.modelEquiv.surjective
    PrimitiveAffineDegreeTwoTwistedSingerModels.Row14.normal_generators N hN

theorem topSocle
    (N : {N : Subgroup DegreeTwoTwoAffineSixteenInterfaces.row14.top // N.Normal}) :
    SocleNormalGeneratorBound (DegreeTwoTwoAffineSixteenInterfaces.row14.top ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples top_normal_generators N.1

noncomputable def family :
    DegreeTwoTwoAffineSixteenInterfaces.row14.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoTwoAffineSixteenInterfaces.row14.normalRegistry topSocle

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow14QuotientSocles
end SymmetricSubgroupAsymptotics

end
