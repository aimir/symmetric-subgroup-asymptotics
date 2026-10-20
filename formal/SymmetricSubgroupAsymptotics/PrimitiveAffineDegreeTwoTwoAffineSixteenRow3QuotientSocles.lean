import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow3TwistedTop
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds

/-! Every quotient of the exact original two-affine row3 has socle width2. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow3QuotientSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

theorem top_normal_generators
    (N : Subgroup DegreeTwoTwoAffineSixteenInterfaces.row3.top) (hN : N.Normal) :
    ∃ x : Fin 2 → DegreeTwoTwoAffineSixteenInterfaces.row3.top,
      Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective
    PrimitiveAffineDegreeTwoTwoAffineSixteenRow3TwistedTop.modelEquiv.toMonoidHom
    PrimitiveAffineDegreeTwoTwoAffineSixteenRow3TwistedTop.modelEquiv.surjective
    PrimitiveAffineDegreeTwoTwistedSingerModels.Row3.normal_generators N hN

theorem topSocle
    (N : {N : Subgroup DegreeTwoTwoAffineSixteenInterfaces.row3.top // N.Normal}) :
    SocleNormalGeneratorBound (DegreeTwoTwoAffineSixteenInterfaces.row3.top ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples top_normal_generators N.1

noncomputable def family :
    DegreeTwoTwoAffineSixteenInterfaces.row3.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoTwoAffineSixteenInterfaces.row3.normalRegistry topSocle

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow3QuotientSocles
end SymmetricSubgroupAsymptotics

end
