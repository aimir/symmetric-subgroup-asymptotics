import SymmetricSubgroupAsymptotics.CFSGSufficientSimpleIndexBounds

/-! A common numerical endpoint for the actual M23/M24 incidence bounds.
The elementary inequality 2^13 ≤ 23^3 pays the sharp outer budget.
No finite capacity or model correspondence is asserted here. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuPrimeTwentyThreeOuterNumerics
open PrimitiveSocleRawStructure

theorem sufficient_budget_of_le_thirteen (ell out : ℕ)
    (hell : 23 ≤ ell) (hout : out ≤ 13) : SufficientOuterOrderBudget ell out := by
  have hpower : (2 : ℕ)^13 ≤ ell^3 :=
    (by decide : (2 : ℕ)^13 ≤ 23^3).trans (Nat.pow_le_pow_left hell 3)
  have hpowerR : (2 : ℝ)^13 ≤ (ell : ℝ)^3 := by exact_mod_cast hpower
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (2 : ℝ)^13) hpowerR
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one, Nat.cast_ofNat] at hlog
  have houtR : (out : ℝ) ≤ 13 := by exact_mod_cast hout
  exact SufficientOuterOrderBudget.of_sharp (by omega) (by linarith)

end SymmetricSubgroupAsymptotics.CFSGMathieuPrimeTwentyThreeOuterNumerics
