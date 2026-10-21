import SymmetricSubgroupAsymptotics.BinaryActionRegistry8
import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.FinCases

/-! Exact original orders and the binary-group property of the twenty-six
checked action rows. No action-completeness assertion is used here. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryDegreeEightRegistryGroupFacts

open BinaryActionRegistry8

theorem exact_card (i : Fin 26) : Nat.card (actions i) = registry.size i := by
  fin_cases i
  · exact BinaryMenuCayley8T1.exact_card
  · exact BinaryMenuCayley8T2.exact_card
  · exact BinaryMenuCayley8T3.exact_card
  · exact BinaryMenuCayley8T4.exact_card
  · exact BinaryMenuCayley8T5.exact_card
  · exact BinaryMenuCayley8T6.exact_card
  · exact BinaryMenuCayley8T7.exact_card
  · exact BinaryMenuCayley8T8.exact_card
  · exact BinaryMenuCayley8T9.exact_card
  · exact BinaryMenuCayley8T10.exact_card
  · exact BinaryMenuCayley8T11.exact_card
  · exact BinaryMenuCayley8T15.exact_card
  · exact BinaryMenuCayley8T16.exact_card
  · exact BinaryMenuCayley8T17.exact_card
  · exact BinaryMenuCayley8T18.exact_card
  · exact BinaryMenuCayley8T19.exact_card
  · exact BinaryMenuCayley8T20.exact_card
  · exact BinaryMenuCayley8T21.exact_card
  · exact BinaryMenuCayley8T22.exact_card
  · exact BinaryMenuCayley8T26.exact_card
  · exact BinaryMenuCayley8T27.exact_card
  · exact BinaryMenuCayley8T28.exact_card
  · exact BinaryMenuCayley8T29.exact_card
  · exact BinaryMenuCayley8T30.exact_card
  · exact BinaryMenuCayley8T31.exact_card
  · exact BinaryMenuCayley8T35.exact_card

def exponent : Fin 26 → ℕ :=
  ![3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5,
    6, 6, 6, 6, 6, 6, 7]

theorem card_pow (i : Fin 26) : Nat.card (actions i) = 2 ^ exponent i := by
  rw [exact_card]
  fin_cases i <;> decide +kernel

theorem isPGroup (i : Fin 26) : IsPGroup 2 (actions i) :=
  IsPGroup.of_card (card_pow i)

end SymmetricSubgroupAsymptotics.BinaryDegreeEightRegistryGroupFacts

end
