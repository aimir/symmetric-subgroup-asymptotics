import SymmetricSubgroupAsymptotics.CFSGSufficientSimpleIndexNumerics
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex
import SymmetricSubgroupAsymptotics.NonabelianSimpleProperIndex

/-! An internal sufficient boundary, strictly separated from the unchanged
published coefficient-three theorem. This is not installed as a public
assumption: actual model proofs must supply it before a final CFSG endpoint
can consume it. The small bounds retain the original finite frontiers. -/
set_option autoImplicit false
noncomputable section
open scoped IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

structure SufficientOuterOrderBudget (ell out : ℕ) : Prop where
  log_six : (out : ℝ) ≤ 6 * Real.logb 2 ell
  log_three_of_small : ell < 27 → (out : ℝ) ≤ 3 * Real.logb 2 ell
  le_twentyFour_of_small : ell < 30 → out ≤ 24

namespace SufficientOuterOrderBudget

theorem mono {ell a b : ℕ} (h : SufficientOuterOrderBudget ell b) (hab : a ≤ b) :
    SufficientOuterOrderBudget ell a := by
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  exact ⟨habR.trans h.log_six, fun he => habR.trans (h.log_three_of_small he),
    fun he => hab.trans (h.le_twentyFour_of_small he)⟩

theorem of_sharp {ell out : ℕ} (hell : 5 ≤ ell)
    (hout : (out : ℝ) ≤ 3 * Real.logb 2 ell) :
    SufficientOuterOrderBudget ell out := by
  have hL : 0 ≤ Real.logb 2 (ell : ℝ) :=
    Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast (show 1 ≤ ell by omega))
  refine ⟨by linarith, fun _ => hout, ?_⟩
  intro hs
  have he : (ell : ℝ) ≤ (2 : ℝ) ^ 5 := by
    exact_mod_cast (show ell ≤ 2 ^ 5 by omega)
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast (show 0 < ell by omega)) he
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hl
  norm_num at hl
  have ho : (out : ℝ) ≤ 24 := by linarith
  exact_mod_cast ho

theorem square_bound {ell out : ℕ} (h : SufficientOuterOrderBudget ell out)
    (hell : 5 ≤ ell) : 4 * out ≤ ell ^ 2 := by
  by_cases hs : ell < 27
  · exact primitive_outerOrder_square_bound ell out hell (h.log_three_of_small hs)
  · exact CFSGSufficientSimpleIndexNumerics.square_bound (by omega) h.log_six

theorem log_six_of_le {ell out r : ℕ} (h : SufficientOuterOrderBudget ell out)
    (hell : 0 < ell) (her : ell ≤ r) : (out : ℝ) ≤ 6 * Real.logb 2 r := by
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast hell) (by exact_mod_cast her : (ell : ℝ) ≤ r)
  linarith [h.log_six]

theorem rounding_gap {ell out r : ℕ} (h : SufficientOuterOrderBudget ell out)
    (hell : 0 < ell) (her : ell ≤ r) (hr : 27 ≤ r) (h63 : r ≤ 63) :
    max 2 out + 1 ≤ evenWidth r := by
  by_cases h30 : r < 30
  · exact CFSGSufficientSimpleIndexNumerics.rounding_gap_of_le_twentyFour hr
      (h.le_twentyFour_of_small (by omega))
  · exact CFSGSufficientSimpleIndexNumerics.rounding_gap_thirtyToSixtyThree
      (by omega) h63 (h.log_six_of_le hell her)

end SufficientOuterOrderBudget

def SufficientSimpleIndexBounds : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
    ¬ IsMulCommutative S → ∀ ell : ℕ, LeastProperIndex S ell →
      ell ^ 2 < Nat.card S ∧ SufficientOuterOrderBudget ell (Nat.card (Outer S))

theorem sufficientSimpleIndexBounds_of_published (h : PublishedSimpleIndexBounds) :
    SufficientSimpleIndexBounds := by
  intro S _ _ _ hn ell he
  obtain ⟨ho, hb⟩ := h S hn ell he
  have hf : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
    (fun hc => hn (isMulCommutative_iff.mpr hc)) he.1
  exact ⟨ho, SufficientOuterOrderBudget.of_sharp hf hb⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
