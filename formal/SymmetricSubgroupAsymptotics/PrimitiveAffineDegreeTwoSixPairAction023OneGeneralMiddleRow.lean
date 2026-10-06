import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction023OneGeneralNormalChain

/-! # Action 023 one-general pilot: middle quotient row -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoSixPairAction023OneGeneralSplit

open Non2UnipotentPrefixFiniteMenu

noncomputable def stateMiddleSocleGenerator :
    SocleNormalGeneratorBound
      (degreeTwoSixPairAction023CheckedLiteral.G ⧸
        (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex
          stateMiddle).1) 1 :=
  chainData.middleQuotientSocleGenerator

end PrimitiveAffineDegreeTwoSixPairAction023OneGeneralSplit
end SymmetricSubgroupAsymptotics

end
