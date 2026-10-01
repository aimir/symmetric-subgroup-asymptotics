import SymmetricSubgroupAsymptotics.MarkedC4MomentGraphs
import SymmetricSubgroupAsymptotics.MarkedC4PsiAnalysis
import SymmetricSubgroupAsymptotics.MarkerDefectSum

/-!
# From the explicit marked-word error to the global asymptotic moment

The RDT reduction naturally produces a fixed-`K` error of size
`A_K (b+r) log(b+r+2)`.  This file proves once that such an explicit uniform
estimate implies the epsilon formulation consumed by the F20 owner.
-/

set_option autoImplicit false
noncomputable section
open Filter

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Quantitative form of the marked moment.  For every fixed linear range of
marks, one constant controls the complete finite error uniformly in `r`. -/
def GlobalMarkedC4ExplicitErrorBound : Prop :=
  ∀ K : ℝ, ∃ A : ℝ, 0 ≤ A ∧ ∀ b r : ℕ, (r : ℝ) ≤ K * b →
    markedC4Moment b r ≤
      (2 : ℝ) ^
        (MarkedC4.markedF b r +
          A * ((b : ℝ) + r) * Real.log ((b : ℝ) + r + 2))

/-- The explicit RDT error is `o((b+r)^2)`, uniformly for `r/b` in a fixed
bounded interval. -/
theorem globalMarkedC4MomentBound_of_explicitError
    (H : GlobalMarkedC4ExplicitErrorBound) :
    GlobalMarkedC4MomentBound := by
  intro ε hε K
  obtain ⟨A, hA, hbound⟩ := H K
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    (MarkerDefectSum.eventually_log_error_le_linear A hA hε)
  filter_upwards [eventually_ge_atTop B] with b hb
  intro r hr
  have hBr : B ≤ b + r := hb.trans (Nat.le_add_right b r)
  have hlog := hB (b + r) hBr
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hbr0 : (0 : ℝ) ≤ (b : ℝ) + r := add_nonneg hb0 hr0
  have herror :
      A * ((b : ℝ) + r) * Real.log ((b : ℝ) + r + 2) ≤
        ε * ((b : ℝ) + r) ^ 2 := by
    push_cast at hlog
    have hm := mul_le_mul_of_nonneg_right hlog hbr0
    nlinarith
  refine (hbound b r hr).trans ?_
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  unfold MarkedC4.markedF
  linarith

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
