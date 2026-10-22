import SymmetricSubgroupAsymptotics.CFSGIntegralGramParityRootCount
import SymmetricSubgroupAsymptotics.CFSGExceptionalNormTwoFinite

/-! A uniform crude root-count bound for the literal pinned E6/E7/E8
norm-two lattices. Only the already-checked rectangular Gram matrices
and their explicitly displayed parity entries are used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalRootCountBound
open CFSGNormTwoRootPairing CFSGExceptionalIntegralGram CFSGExceptionalNormTwoFinite
open CFSGExceptionalCartanPositiveDefinite CFSGIntegralGramParityRootCount

theorem gramSix_parity (i : Fin 8) (j : Fin 6) : gramSix i j%2=if j=0 then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> decide
theorem gramSeven_parity (i : Fin 8) (j : Fin 7) : gramSeven i j%2=if j=0 then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> decide
theorem gramEight_parity (i j : Fin 8) : integerColumns i j%2=if j=0 then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> decide

theorem E6_root_card_le : Nat.card (Roots CartanMatrix.E₆)≤512 :=
  roots_card_le CartanMatrix.E₆ E6_positive_definite gramSix gramSix_identity 0 gramSix_parity
theorem E7_root_card_le : Nat.card (Roots CartanMatrix.E₇)≤512 :=
  roots_card_le CartanMatrix.E₇ E7_positive_definite gramSeven gramSeven_identity 0 gramSeven_parity
theorem E8_root_card_le : Nat.card (Roots CartanMatrix.E₈)≤512 :=
  roots_card_le CartanMatrix.E₈ E8_positive_definite integerColumns integerColumns_gram 0 gramEight_parity

end SymmetricSubgroupAsymptotics.CFSGExceptionalRootCountBound
