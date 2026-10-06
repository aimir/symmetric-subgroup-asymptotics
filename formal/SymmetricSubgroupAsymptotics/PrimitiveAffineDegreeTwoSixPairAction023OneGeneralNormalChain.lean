import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction023OneGeneralMiddleCertificate
import SymmetricSubgroupAsymptotics.FiniteThreeNormalChainSocleGenerators

/-!
# Action 023 one-general pilot: checked three-state chain

This module consumes the separately checked four-row middle certificate and
the complete normal registry.  It contains no finite table construction and
exports only the generic chain datum used by the three quotient rows.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoSixPairAction023OneGeneralSplit

open Non2UnipotentPrefixFiniteMenu

private theorem originalCard : Nat.card Original = 12 := by
  calc
    Nat.card Original =
        Nat.card PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.Source :=
      Nat.card_congr
        PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv.symm.toEquiv
    _ = 12 :=
      PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.source_card

private theorem topCard : Nat.card (⊤ : Subgroup Original) = 12 := by
  calc
    Nat.card (⊤ : Subgroup Original) = Nat.card Original :=
      Nat.card_congr Subgroup.topEquiv.toEquiv
    _ = 12 := originalCard

private theorem middle_ne_top :
    (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex stateMiddle).1 ≠
      ⊤ := by
  intro h
  have hcard :=
    congrArg (fun H : Subgroup Original => Nat.card H) h
  change
    Nat.card
        ((degreeTwoSixPairAction023CheckedLiteral.normalStateIndex
          stateMiddle).1) =
      Nat.card (⊤ : Subgroup Original) at hcard
  rw [middleCard, topCard] at hcard
  norm_num at hcard

private theorem normal_eq_bot_or_middle_or_top
    (N : Subgroup Original) (hN : N.Normal) :
    N = ⊥ ∨
      N = (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex
        stateMiddle).1 ∨ N = ⊤ := by
  letI : N.Normal := hN
  obtain ⟨i, hi⟩ :=
    PrimitiveAffineDegreeTwoSixPairAction023CatalogueRow.normal_complete N
  fin_cases i
  · have hiZero :
        (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex stateZero).1 =
          N := by
      change Subgroup.closure
        (Set.range
          (PrimitiveAffineDegreeTwoSixPairAction023CatalogueRow.stateGenerators 0)) = N
      exact hi
    exact Or.inl (hiZero.symm.trans stateZero_eq_bot)
  · have hiMiddle :
        (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex
          stateMiddle).1 = N := by
      change Subgroup.closure
        (Set.range
          (PrimitiveAffineDegreeTwoSixPairAction023CatalogueRow.stateGenerators 1)) = N
      exact hi
    exact Or.inr (Or.inl hiMiddle.symm)
  · have hiTop :
        (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex stateTop).1 =
          N := by
      change Subgroup.closure
        (Set.range
          (PrimitiveAffineDegreeTwoSixPairAction023CatalogueRow.stateGenerators 2)) = N
      exact hi
    exact Or.inr (Or.inr (hiTop.symm.trans stateTop_eq_top))

noncomputable def chainData : FiniteThreeNormalChainData Original where
  middle :=
    (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex stateMiddle).1
  middle_normal := inferInstance
  middle_ne_bot := middle_ne_bot
  middle_ne_top := middle_ne_top
  normal_eq_bot_or_middle_or_top := normal_eq_bot_or_middle_or_top
  generator :=
    degreeTwoSixPairAction023CheckedLiteral.stateGenerators
      stateMiddle genZero
  generator_mem := middleGenerator_mem
  generator_ne_one := middleGenerator_ne_one

end PrimitiveAffineDegreeTwoSixPairAction023OneGeneralSplit
end SymmetricSubgroupAsymptotics

end
