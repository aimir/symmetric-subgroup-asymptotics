import SymmetricSubgroupAsymptotics.CharacteristicChiefPrimeMultiplicityBudget
import SymmetricSubgroupAsymptotics.BinaryAffineJointSelectedWindowNumerics

/-! Exact odd-prime multiplicities of the actual binary GL4 and GL5
orders. The only finite reductions are the two natural-number order
factorizations, not group elements or subgroup catalogues. Genuine
elementary-order divisibility gives the corresponding joint dimension
budgets for any actual chief profile. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryGeneralLinearPrimeMultiplicity
open CharacteristicChiefPrimeMultiplicityBudget CharacteristicChiefPrimePowerCosts
open ActualWreathChiefOrderDivisibility

theorem GL_four_odd_multiplicity :
    primeMultiplicityAway 2 (Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))) = 4 := by
  rw [BinaryAffineJointSelectedWindowNumerics.matrix_GL_card_eq_order]
  change primeMultiplicityAway 2 20160 = 4
  decide +kernel

theorem GL_five_odd_multiplicity :
    primeMultiplicityAway 2 (Nat.card (Matrix.GeneralLinearGroup (Fin 5) (ZMod 2))) = 5 := by
  rw [BinaryAffineJointSelectedWindowNumerics.matrix_GL_card_eq_order]
  change primeMultiplicityAway 2 9999360 = 5
  decide +kernel

theorem otherDimension_le_four {t cost localOrder : ℕ}
    (P : DivisibleProfile t cost localOrder)
    (hd : localOrder ∣ Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))) :
    otherDimensionAt 2 P.charges ≤ 4 :=
  (otherDimension_le_primeMultiplicityAway P 2 _
    (Nat.card_pos (α := Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))).ne' hd).trans_eq
      GL_four_odd_multiplicity

theorem otherDimension_le_five {t cost localOrder : ℕ}
    (P : DivisibleProfile t cost localOrder)
    (hd : localOrder ∣ Nat.card (Matrix.GeneralLinearGroup (Fin 5) (ZMod 2))) :
    otherDimensionAt 2 P.charges ≤ 5 :=
  (otherDimension_le_primeMultiplicityAway P 2 _
    (Nat.card_pos (α := Matrix.GeneralLinearGroup (Fin 5) (ZMod 2))).ne' hd).trans_eq
      GL_five_odd_multiplicity

end SymmetricSubgroupAsymptotics.BinaryGeneralLinearPrimeMultiplicity
