import SymmetricSubgroupAsymptotics.MarkedC4ActualSingleGlobalHallPolynomial
import SymmetricSubgroupAsymptotics.MarkedC4ErrorCalculus

/-! Absorb the ONE global Hall polynomial P(r)=16(r+1)^2 after the entire
physical recurrence. This does not justify paying it at every peel. The
initial physical-degree-zero row may retain P(r), as required when vertical
marker subgroups are included in the enlarged counted family. -/
set_option autoImplicit false
noncomputable section
open Filter
namespace SymmetricSubgroupAsymptotics.MarkedC4.SingleMarkError

def error (_b r : ℕ) : ℝ := Real.logb 2 (VerticalHallBase.polynomial r)

theorem polynomial_eq_exp (b r : ℕ) :
    VerticalHallBase.polynomial r = (2 : ℝ)^(error b r) := by
  exact (Real.rpow_logb (by norm_num : (0 : ℝ)<2) (by norm_num : (2 : ℝ)≠1)
    (show 0 < VerticalHallBase.polynomial r by unfold VerticalHallBase.polynomial; positivity)).symm

theorem error_le_boundedWordError {b : ℕ} (hb : 1 ≤ b) (r : ℕ) :
    error b r ≤ boundedWordError 5 b r := by
  let s : ℝ := (b : ℝ)+r+2
  have hs : 2 ≤ s := by
    dsimp [s]
    linarith [Nat.cast_nonneg (α := ℝ) b,Nat.cast_nonneg (α := ℝ) r]
  have hr : (r : ℝ)+1 ≤ s := by
    dsimp [s]
    linarith [Nat.cast_nonneg (α := ℝ) b]
  have hfour : (16 : ℝ) ≤ s^4 := by
    calc (16 : ℝ) = (2 : ℝ)^4 := by norm_num
         _ ≤ s^4 := by gcongr
  have hpoly : VerticalHallBase.polynomial r ≤ s^(6*b) := by
    unfold VerticalHallBase.polynomial
    calc
      16*((r : ℝ)+1)^2 ≤ s^4*s^2 := by gcongr
      _ = s^6 := by ring
      _ ≤ s^(6*b) := by
        exact pow_le_pow_right₀ (by linarith : 1 ≤ s) (by omega)
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
    (show 0 < VerticalHallBase.polynomial r by unfold VerticalHallBase.polynomial; positivity) hpoly
  unfold error
  apply hlog.trans_eq
  rw [Real.logb_pow]
  unfold boundedWordError Real.logb
  dsimp [s]
  push_cast
  ring

theorem negligible : UniformQuadraticNegligible error := by
  intro ε hε K
  filter_upwards [eventually_ge_atTop 1,
    boundedWordError_negligible (A := 5) (by norm_num) ε hε K] with b hb hsmall
  intro r hr
  exact (error_le_boundedWordError hb r).trans (hsmall r hr)

/-- A once-global P(r) factor is absorbed AFTER a proved physical error.
This is a numerical composition theorem, not a subgroup-count premise. -/
theorem absorb {count e : ℕ → ℕ → ℝ}
    (hcount : ∀ b r, count b r ≤ VerticalHallBase.polynomial r *
      (2 : ℝ)^(markedF b r + e b r))
    (he : UniformQuadraticNegligible e) :
    ∀ ε : ℝ, 0 < ε → ∀ K : ℝ, ∀ᶠ b : ℕ in atTop, ∀ r : ℕ,
      (r : ℝ) ≤ K*b → count b r ≤
        (2 : ℝ)^(markedF b r + ε*((b : ℝ)+r)^2) := by
  apply markedMomentBound_of_error (e := fun b r => error b r + e b r) _ (negligible.add he)
  intro b r
  apply (hcount b r).trans_eq
  rw [polynomial_eq_exp b r,← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
  congr 1
  ring

end SymmetricSubgroupAsymptotics.MarkedC4.SingleMarkError
end
