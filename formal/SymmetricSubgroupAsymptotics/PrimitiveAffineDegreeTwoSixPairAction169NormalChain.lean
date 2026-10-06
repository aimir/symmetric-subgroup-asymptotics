import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169NormalStateBounds
import SymmetricSubgroupAsymptotics.FiniteThreeNormalChainSocleGenerators
import Mathlib.Tactic.FinCases

/-!
# Selected six-pair action 169: checked three-state normal chain

This module combines the literal sign bounds with the surjective checked
normal registry.  It exports only the reusable chain datum.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ThreeNormalChain

open Non2UnipotentPrefixFiniteMenu

private theorem normal_eq_bot_or_middle_or_top
    (N : Subgroup Original) (hN : N.Normal) :
    N = ⊥ ∨
      N = (degreeTwoSixPairAction169CheckedLiteral.normalStateIndex
        stateMiddle).1 ∨ N = ⊤ := by
  letI : N.Normal := hN
  obtain ⟨i, hi⟩ := PrimitiveAffineDegreeTwoSixPairAction169CatalogueRow.normal_complete N
  fin_cases i
  · have hiZero :
        (degreeTwoSixPairAction169CheckedLiteral.normalStateIndex stateZero).1 =
          N := by
      change Subgroup.closure
        (Set.range (PrimitiveAffineDegreeTwoSixPairAction169CatalogueRow.stateGenerators 0)) = N
      exact hi
    exact Or.inl (hiZero.symm.trans stateZero_eq_bot)
  · have hiMiddle :
        (degreeTwoSixPairAction169CheckedLiteral.normalStateIndex
          stateMiddle).1 = N := by
      change Subgroup.closure
        (Set.range (PrimitiveAffineDegreeTwoSixPairAction169CatalogueRow.stateGenerators 1)) = N
      exact hi
    exact Or.inr (Or.inl hiMiddle.symm)
  · have hiTop :
        (degreeTwoSixPairAction169CheckedLiteral.normalStateIndex stateTop).1 =
          N := by
      change Subgroup.closure
        (Set.range (PrimitiveAffineDegreeTwoSixPairAction169CatalogueRow.stateGenerators 2)) = N
      exact hi
    exact Or.inr (Or.inr (hiTop.symm.trans stateTop_eq_top))

noncomputable def chainData : FiniteThreeNormalChainData Original where
  middle :=
    (degreeTwoSixPairAction169CheckedLiteral.normalStateIndex stateMiddle).1
  middle_normal := inferInstance
  middle_ne_bot := stateMiddle_ne_bot
  middle_ne_top := stateMiddle_ne_top
  normal_eq_bot_or_middle_or_top := normal_eq_bot_or_middle_or_top
  generator :=
    degreeTwoSixPairAction169CheckedLiteral.stateGenerators
      stateMiddle middleGenerator
  generator_mem := middleGenerator_mem
  generator_ne_one := middleGenerator_ne_one

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ThreeNormalChain

end
