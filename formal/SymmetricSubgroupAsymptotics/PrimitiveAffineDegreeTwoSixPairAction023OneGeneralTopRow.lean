import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction023OneGeneralNormalChain

/-! # Action 023 one-general pilot: top quotient row -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoSixPairAction023OneGeneralSplit

open Non2UnipotentPrefixFiniteMenu

private noncomputable def topOfEq
    (N : Subgroup Original) [N.Normal] (h : N = ⊤) :
    SocleNormalGeneratorBound (Original ⧸ N) 1 := by
  subst N
  exact
    FiniteThreeNormalChainData.topQuotientSocleGenerator
      (G := Original)

noncomputable def stateTopSocleGenerator :
    SocleNormalGeneratorBound
      (degreeTwoSixPairAction023CheckedLiteral.G ⧸
        (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex stateTop).1) 1 := by
  exact topOfEq _ stateTop_eq_top

end PrimitiveAffineDegreeTwoSixPairAction023OneGeneralSplit
end SymmetricSubgroupAsymptotics

end
