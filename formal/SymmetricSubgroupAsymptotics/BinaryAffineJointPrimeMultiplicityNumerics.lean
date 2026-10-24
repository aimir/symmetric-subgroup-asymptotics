import SymmetricSubgroupAsymptotics.FiniteGroupPrimeMultiplicityGenerators
import SymmetricSubgroupAsymptotics.BinaryAffineJointSelectedWindowNumerics

/-! Joint prime multiplicities of the actual binary GL4 and GL5 orders
pay all three selected affine windows. Only two natural-number
factorizations and scalar inequalities are checked; no group census or
simple-generation assumption enters these certificates. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.BinaryAffineJointPrimeMultiplicityNumerics
open BinaryAffineJointSelectedWindowNumerics NaturalSquareRootQuotientCeiling

theorem GL_four_cardFactors :
    ArithmeticFunction.cardFactors
      (Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)))=10 := by
  rw [matrix_GL_card_eq_order]
  change ArithmeticFunction.cardFactors 20160=10
  decide +kernel

theorem GL_five_cardFactors :
    ArithmeticFunction.cardFactors
      (Nat.card (Matrix.GeneralLinearGroup (Fin 5) (ZMod 2)))=15 := by
  rw [matrix_GL_card_eq_order]
  change ArithmeticFunction.cardFactors 9999360=15
  decide +kernel

def localCost (d e : ℕ) : ℕ :=
  d*e.choose (e/2) + d*(d-1)/2*(e.choose (e/2)-1) +
    ArithmeticFunction.cardFactors (binaryGLOrder d)

theorem four_one : localCost 4 1+1 ≤ quotientCeiling (2^5) 5 := by
  decide +kernel

theorem four_two : localCost 4 2+3 ≤ quotientCeiling (2^6) 6 := by
  decide +kernel

theorem five_one : localCost 5 1+1 ≤ quotientCeiling (2^6) 6 := by
  decide +kernel

end SymmetricSubgroupAsymptotics.BinaryAffineJointPrimeMultiplicityNumerics
