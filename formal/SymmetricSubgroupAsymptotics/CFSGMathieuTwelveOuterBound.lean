import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveAcceptedCodeCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveOuterBudgetOfFixedCapacity

/-! The complete actual fixed-generator capacity discharges the M12 outer
budget internally. The normalizer inequality gives outer order at most
five, and the proved least-index lower bound pays the logarithmic budget. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveOuterBound
open CFSG.Certificates.Mathieu12 PrimitiveSocleRawStructure

theorem original_outer_card_le_five [IsSimpleGroup CFSG.Models.Presentations.M12.Model] :
    Nat.card (Outer M12) ≤ 5 := by
  have hw := CFSGMathieuTwelveOuterBudgetOfFixedCapacity.original_outer_mul_twentyTwo_le_ten_fixed
  have hc := CFSGMathieuTwelveAcceptedCodeCapacity.fixedAutomorphisms_card_le_eleven
  omega

theorem outer_card_le_five [IsSimpleGroup CFSG.Models.Presentations.M12.Model] :
    Nat.card (Outer CFSG.Models.Presentations.M12.Model) ≤ 5 := by
  rw [CFSGReduction.outer_card_congr CFSGMathieuTwelveActualEquivalence.actualEquivalence]
  exact original_outer_card_le_five

theorem original_outer_card_le_ten [IsSimpleGroup CFSG.Models.Presentations.M12.Model] :
    Nat.card (Outer M12) ≤ 10 :=
  original_outer_card_le_five.trans (by decide)

theorem outer_card_le_ten [IsSimpleGroup CFSG.Models.Presentations.M12.Model] :
    Nat.card (Outer CFSG.Models.Presentations.M12.Model) ≤ 10 :=
  outer_card_le_five.trans (by decide)

theorem sufficient_outer_budget [Finite CFSG.Models.Presentations.M12.Model]
    [IsSimpleGroup CFSG.Models.Presentations.M12.Model] (ell : ℕ)
    (hell : LeastProperIndex CFSG.Models.Presentations.M12.Model ell) :
    SufficientOuterOrderBudget ell (Nat.card (Outer CFSG.Models.Presentations.M12.Model)) := by
  have he := CFSGMathieuTwelveOuterBudgetOfFixedCapacity.least_index_ge_eleven ell hell
  have hlog : (2 : ℝ) ≤ Real.logb 2 ell := by
    have hle : (2 : ℝ)^2 ≤ (ell : ℝ) := by
      exact_mod_cast (show (2 : ℕ)^2 ≤ ell by omega)
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < (2 : ℝ)^2) hle
    simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
      mul_one,Nat.cast_ofNat] using h
  have hout : (Nat.card (Outer CFSG.Models.Presentations.M12.Model) : ℝ) ≤ 5 := by
    exact_mod_cast outer_card_le_five
  exact SufficientOuterOrderBudget.of_sharp (by omega) (by linarith)

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveOuterBound
