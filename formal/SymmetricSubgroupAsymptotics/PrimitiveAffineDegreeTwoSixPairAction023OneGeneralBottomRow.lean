import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction023OneGeneralNormalChain

/-! # Action 023 one-general pilot: bottom quotient row -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoSixPairAction023OneGeneralSplit

open Non2UnipotentPrefixFiniteMenu

private noncomputable def bottomOfEq
    (N : Subgroup Original) [N.Normal] (h : N = ⊥) :
    SocleNormalGeneratorBound (Original ⧸ N) 1 := by
  subst N
  exact chainData.bottomQuotientSocleGenerator

noncomputable def stateZeroSocleGenerator :
    SocleNormalGeneratorBound
      (degreeTwoSixPairAction023CheckedLiteral.G ⧸
        (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex stateZero).1) 1 := by
  exact bottomOfEq _ stateZero_eq_bot

end PrimitiveAffineDegreeTwoSixPairAction023OneGeneralSplit
end SymmetricSubgroupAsymptotics

end
