import SymmetricSubgroupAsymptotics.BinaryMixtureNumerics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Uniform numerical absorption for the two complete-mixture regimes.
The Hall exponent retains the actual terminal correction 7, and the
critical coefficient shift retains its full removed half-degree 2a+4T.
The large-carrier conclusion explicitly requires the original small-support
cutoff. No subgroup count, profile coverage, or physical weight is assumed
or asserted by these scalar statements.
-/
set_option autoImplicit false
open Filter

namespace SymmetricSubgroupAsymptotics.BinaryMixtureNumerics

/-- The explicit Hall exponent, including the terminal correction, loses
aN/25 up to a linear cost. Here N is the complete physical half-degree. -/
theorem hall_exponent_le_mixture (R a u T : ℝ) (hR : 0 ≤ R)
    (ha : 1 ≤ a) (hu : 0 ≤ u) (hT : 0 ≤ T)
    (huT : u ≤ 7*T) (hTa : T ≤ a/140) :
    (a+u+7)^2/3 + (a^2+(R+a+u)^2)/4 ≤
      (R+2*a+4*T)^2/4 - a*(R+2*a+4*T)/25 + 22*a := by
  have ha0 : 0 ≤ a := by linarith
  have hua : u ≤ a/20 := by linarith
  have hfixed : (14/3)*(a+u)+49/3 ≤ 22*a := by linarith
  have hdef := hall_deficit_le_mixture R a u T hR ha0 hu huT hTa
  have hmono : (R+2*a)^2 ≤ (R+2*a+4*T)^2 := by
    nlinarith [mul_nonneg hR hT, mul_nonneg ha0 hT, sq_nonneg T]
  nlinarith [sq_nonneg u]

/-- A general critical-coefficient shift cost. The shift h is bounded by
b; the estimate does not replace h by a carrier count. -/
theorem critical_shift_log_cost_le (N h b : ℝ) (hN : 1 ≤ N)
    (hh : 0 ≤ h) (hhb : h ≤ b) :
    h * Real.log (2*N) / Real.log 2 ≤
      (2 / Real.log 2) * b * Real.log (N+2) := by
  have hNpos : 0 < N := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log (2*N) ≤ 2 * Real.log (N+2) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hNpos.ne']
    have h₁ := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ N+2 by linarith)
    have h₂ := Real.log_le_log hNpos (show N ≤ N+2 by linarith)
    linarith
  have hlog0 : 0 ≤ Real.log (N+2) := Real.log_nonneg (by linarith)
  calc
    _ ≤ h * (2 * Real.log (N+2)) / Real.log 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hh) hlog2.le
    _ ≤ b * (2 * Real.log (N+2)) / Real.log 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hhb (by positivity)) hlog2.le
    _ = _ := by ring

/-- The actual Hall exponent and the whole critical coefficient shift
already have the small-regime form, with an explicit uniform error constant.
Additional prefactors can subsequently be included in that constant. -/
theorem hall_exponent_with_critical_shift_le (R a u T : ℝ) (hR : 0 ≤ R)
    (ha : 1 ≤ a) (hu : 0 ≤ u) (hT : 0 ≤ T)
    (huT : u ≤ 7*T) (hTa : T ≤ a/140) :
    (a+u+7)^2/3 + (a^2+(R+a+u)^2)/4 - (R+2*a+4*T)^2/4 +
        (2*a+4*T) * Real.log (2*(R+2*a+4*T)) / Real.log 2 ≤
      -a*(R+2*a+4*T)/25 +
        (28 / Real.log 2) * a * Real.log (R+2*a+4*T+2) := by
  have ha0 : 0 ≤ a := by linarith
  have hN : 1 ≤ R+2*a+4*T := by linarith
  have hshift := critical_shift_log_cost_le (R+2*a+4*T) (2*a+4*T) (3*a)
    hN (by positivity) (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (show (2 : ℝ) ≤ R+2*a+4*T+2 by linarith)
  have hlinear : 22*a ≤ (22 / Real.log 2)*a*Real.log (R+2*a+4*T+2) := by
    calc
      _ = (22*a*Real.log 2) / Real.log 2 := by field_simp [hlog2.ne']
      _ ≤ (22*a*Real.log (R+2*a+4*T+2)) / Real.log 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog (by positivity)) hlog2.le
      _ = _ := by ring
  have hhall := hall_exponent_le_mixture R a u T hR ha hu hT huT hTa
  have hhall' : (a+u+7)^2/3 + (a^2+(R+a+u)^2)/4 -
      (R+2*a+4*T)^2/4 ≤ -a*(R+2*a+4*T)/25 + 22*a := by
    linarith only [hhall]
  calc
    _ ≤ (-a*(R+2*a+4*T)/25 + 22*a) +
        (2/Real.log 2)*(3*a)*Real.log (R+2*a+4*T+2) :=
      add_le_add hhall' hshift
    _ ≤ (-a*(R+2*a+4*T)/25 +
        (22/Real.log 2)*a*Real.log (R+2*a+4*T+2)) +
        (2/Real.log 2)*(3*a)*Real.log (R+2*a+4*T+2) :=
      add_le_add (add_le_add le_rfl hlinear) le_rfl
    _ = _ := by ring

/-- The original noncritical half-support cutoff and the large-carrier
regime force a square-root lower bound on carrier mass. -/
theorem large_regime_mass_lower (N a T : ℝ)
    (hlarge : a/140 < T) (hsupport : Real.sqrt N / 4 < 2*a+4*T) :
    Real.sqrt N / 1136 < T := by
  linarith

/-- The same support implication for any fixed positive cutoff denominator. -/
theorem large_regime_mass_lower_of_cutoff (N a T q : ℝ) (hq : 0 < q)
    (hlarge : a/140 < T) (hsupport : Real.sqrt N / q < 2*a+4*T) :
    Real.sqrt N / (284*q) < T := by
  apply (div_lt_iff₀ (show 0 < 284*q by positivity)).mpr
  have h₁ := (div_lt_iff₀ hq).mp hsupport
  have h₂ := mul_lt_mul_of_pos_right (show 2*a+4*T < 284*T by linarith) hq
  nlinarith

/-- A fixed logarithmic cost is uniformly smaller than any positive
multiple of the square root. The threshold depends only on C and epsilon. -/
theorem eventually_log_error_le_sqrt (C : ℝ) (hC : 0 ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      C * Real.log ((n : ℝ)+2) ≤ ε * Real.sqrt (n : ℝ) := by
  let δ : ℝ := ε / (2*(C+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hshift : Tendsto (fun n : ℕ => (n : ℝ)+2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hlog := ((_root_.isLittleO_log_rpow_atTop
    (by norm_num : (0 : ℝ) < 1/2)).bound hδ)
  filter_upwards [hshift.eventually hlog, eventually_ge_atTop 1] with n hn hn1
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hlog0 : 0 ≤ Real.log ((n : ℝ)+2) := Real.log_nonneg (by linarith)
  have hsqrt : Real.sqrt ((n : ℝ)+2) ≤ 2*Real.sqrt (n : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hn0]
  have hlogbound : Real.log ((n : ℝ)+2) ≤ δ * Real.sqrt ((n : ℝ)+2) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog0,
      abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ)+2) _),
      ← Real.sqrt_eq_rpow, abs_of_nonneg (Real.sqrt_nonneg _)] using hn
  have hδbound : C * (2*δ) ≤ ε := by
    have heq : C * (2*δ) = ε*C/(C+1) := by
      dsimp [δ]
      field_simp [show C+1 ≠ 0 by positivity]
      <;> ring
    rw [heq]
    exact (div_le_iff₀ (show 0 < C+1 by positivity)).mpr (by nlinarith)
  calc
    C * Real.log ((n : ℝ)+2) ≤ C * (δ * Real.sqrt ((n : ℝ)+2)) :=
      mul_le_mul_of_nonneg_left hlogbound hC
    _ ≤ C * (δ * (2*Real.sqrt (n : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsqrt hδ.le) hC
    _ = (C*(2*δ)) * Real.sqrt (n : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hδbound (Real.sqrt_nonneg _)

/-- Small-regime absorption is uniform over every a at least one. -/
theorem eventually_small_regime_exponent_le (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, 1 ≤ a →
      -a*(n : ℝ)/25 + C*a*Real.log ((n : ℝ)+2) ≤ -(n : ℝ)/50 := by
  filter_upwards [eventually_log_error_le_sqrt C hC
    (by norm_num : (0 : ℝ) < 1/50), eventually_ge_atTop 1] with n hn hn1
  intro a ha
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hnprod := mul_nonneg (sub_nonneg.mpr hnreal) hn0
  have hsqrt : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨hn0, by nlinarith⟩
  have hlog : C * Real.log ((n : ℝ)+2) ≤ (n : ℝ)/50 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ a by linarith)
  have han : (n : ℝ) ≤ a*(n : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ (n : ℝ) by positivity)]
  nlinarith

/-- The large-regime logarithmic error is absorbed uniformly over the
original parameters once their physical support exceeds the cutoff. -/
theorem eventually_large_regime_exponent_le (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ a T : ℝ,
      a/140 < T → Real.sqrt (n : ℝ)/4 < 2*a+4*T →
      -(29/656)*T*(n : ℝ) + C*(n : ℝ)*Real.log ((n : ℝ)+2) ≤
        -(29/1490432)*(n : ℝ) := by
  filter_upwards [eventually_log_error_le_sqrt C hC
    (by norm_num : (0 : ℝ) < 29/1490432), eventually_ge_atTop 1] with n hn hn1
  intro a T hlarge hsupport
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hsqrt : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr hnreal
  have hmass := (large_regime_mass_lower (n : ℝ) a T hlarge hsupport).le
  have hmassn := mul_le_mul_of_nonneg_right hmass hn0
  have herror := mul_le_mul_of_nonneg_left hn hn0
  have hsqrtn := mul_le_mul_of_nonneg_left hsqrt hn0
  nlinarith

/-- Arbitrary positive support cutoffs are available without changing the
counting argument. In particular q=32 accommodates a narrower original
small-support theorem. -/
theorem eventually_large_regime_exponent_le_of_cutoff (C : ℝ) (hC : 0 ≤ C)
    (q : ℝ) (hq : 0 < q) :
    ∀ᶠ n : ℕ in atTop, ∀ a T : ℝ,
      a/140 < T → Real.sqrt (n : ℝ)/q < 2*a+4*T →
      -(29/656)*T*(n : ℝ) + C*(n : ℝ)*Real.log ((n : ℝ)+2) ≤
        -(29/(372608*q))*(n : ℝ) := by
  let ε : ℝ := 29/(372608*q)
  have hε : 0 < ε := by dsimp [ε]; positivity
  filter_upwards [eventually_log_error_le_sqrt C hC hε,
    eventually_ge_atTop 1] with n hn hn1
  intro a T hlarge hsupport
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hsqrt : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr hnreal
  have hmass := (large_regime_mass_lower_of_cutoff
    (n : ℝ) a T q hq hlarge hsupport).le
  have hloss : 2*ε*Real.sqrt (n : ℝ) ≤ (29/656)*T := by
    calc
      _ = (29/656) * (Real.sqrt (n : ℝ)/(284*q)) := by
        dsimp [ε]
        field_simp [hq.ne']
        <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by norm_num)
  have hlossn := mul_le_mul_of_nonneg_right hloss hn0
  have herror := mul_le_mul_of_nonneg_left hn hn0
  have hsqrtn := mul_le_mul_of_nonneg_left hsqrt hn0
  have hlast := mul_le_mul_of_nonneg_left hsqrtn hε.le
  change _ ≤ -ε*(n : ℝ)
  nlinarith

/-- The narrower cutoff suggested by the direct finite-alphabet
small-support estimate still gives a fixed exponential rate. -/
theorem eventually_large_regime_exponent_le_cutoff32 (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ a T : ℝ,
      a/140 < T → Real.sqrt (n : ℝ)/32 < 2*a+4*T →
      -(29/656)*T*(n : ℝ) + C*(n : ℝ)*Real.log ((n : ℝ)+2) ≤
        -(29/11923456)*(n : ℝ) := by
  simpa only [show (372608 : ℝ)*32 = 11923456 by norm_num] using
    eventually_large_regime_exponent_le_of_cutoff C hC 32 (by norm_num)

/-- Both numerical envelopes have one common exponential decay rate.
The second statement keeps the original support cutoff as an explicit
condition; it is not inferred from a source-group comparison. -/
theorem eventually_two_regime_bounds (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      (∀ a : ℝ, 1 ≤ a →
        (2 : ℝ)^(-a*(n : ℝ)/25+C*a*Real.log ((n : ℝ)+2)) ≤
          (2 : ℝ)^(-(29/1490432)*(n : ℝ))) ∧
      (∀ a T : ℝ, a/140 < T → Real.sqrt (n : ℝ)/4 < 2*a+4*T →
        (2 : ℝ)^(-(29/656)*T*(n : ℝ)+C*(n : ℝ)*Real.log ((n : ℝ)+2)) ≤
          (2 : ℝ)^(-(29/1490432)*(n : ℝ))) := by
  filter_upwards [eventually_small_regime_exponent_le C hC,
    eventually_large_regime_exponent_le C hC] with n hsmall hlarge
  constructor
  · intro a ha
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    have := hsmall a ha
    linarith
  · intro a T hT hsupp
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (hlarge a T hT hsupp)

private theorem constant_le_log_cost (N d : ℝ) (hN : 0 ≤ N) (hd : 0 ≤ d) :
    d ≤ (d / Real.log 2) * Real.log (N+2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (show (2 : ℝ) ≤ N+2 by linarith)
  calc
    _ = (d * Real.log 2) / Real.log 2 := by field_simp [hlog2.ne']
    _ ≤ (d * Real.log (N+2)) / Real.log 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hd) hlog2.le
    _ = _ := by ring

/-- Exact quadratic margin for the finite-alphabet small-support route.
The coefficient 211/192 includes both the tail subgroup count and the
terminal Hall correction before any analytic error is absorbed. -/
theorem small_support_quadratic_le (N C : ℝ) (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hCN : C ≤ Real.sqrt N / 4) :
    -N/2 + (211/192)*C^2 ≤ -(1325/3072)*N := by
  have hsqrt := Real.sqrt_nonneg N
  have hsq := Real.sq_sqrt hN
  have hprod := mul_nonneg (sub_nonneg.mpr hCN)
    (show 0 ≤ Real.sqrt N/4+C by positivity)
  nlinarith

/-- Uniform absorption for the original small-support family. The actual
coefficient shift C and an arbitrary fixed logarithmic prefactor are kept
in the exponent. There is no dependence of the threshold on C. -/
theorem eventually_small_support_exponent_le (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ C : ℝ, 0 ≤ C → C ≤ Real.sqrt (n : ℝ)/4 →
      -(n : ℝ)/2 + 1/2 + (211/192)*C^2 + (14/3)*C + 49/3 +
          C*Real.log (2*(n : ℝ))/Real.log 2 + K*Real.log ((n : ℝ)+2) ≤
        -(n : ℝ)/4 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let A : ℝ := (14/3)/Real.log 2 + 2/Real.log 2
  let B : ℝ := K + (101/6)/Real.log 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  filter_upwards [eventually_log_error_le_sqrt A hA
      (by norm_num : (0 : ℝ) < 1/4),
    eventually_log_error_le_sqrt B hB (by norm_num : (0 : ℝ) < 1/16),
    eventually_ge_atTop 1] with n hAn hBn hn1
  intro C hC hCN
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hsqrt0 := Real.sqrt_nonneg (n : ℝ)
  have hsq := Real.sq_sqrt hn0
  have hsqrt : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨hn0, by nlinarith [mul_nonneg (sub_nonneg.mpr hnreal) hn0]⟩
  have hshift := critical_shift_log_cost_le (n : ℝ) C C hnreal hC le_rfl
  have hconst := constant_le_log_cost (n : ℝ) (14/3) hn0 (by norm_num)
  have hconstC := mul_le_mul_of_nonneg_left hconst hC
  have hfirst : (14/3)*C + C*Real.log (2*(n : ℝ))/Real.log 2 ≤
      C*(A*Real.log ((n : ℝ)+2)) := by
    dsimp [A]
    nlinarith
  have hAnC := mul_le_mul_of_nonneg_left hAn hC
  have hCNsqrt := mul_le_mul_of_nonneg_right hCN (show 0 ≤ Real.sqrt (n : ℝ)/4 by positivity)
  have hfirst' : (14/3)*C + C*Real.log (2*(n : ℝ))/Real.log 2 ≤
      (n : ℝ)/16 := by
    nlinarith
  have hconst' := constant_le_log_cost (n : ℝ) (101/6) hn0 (by norm_num)
  have hsecond : K*Real.log ((n : ℝ)+2) + 101/6 ≤ (n : ℝ)/16 := by
    dsimp [B] at hBn
    nlinarith
  have hquad := small_support_quadratic_le (n : ℝ) C hn0 hC hCN
  nlinarith

/-- The small-support exponent gives actual exponential decay at rate
one quarter, uniformly including every allowed real support value. -/
theorem eventually_small_support_bound (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ C : ℝ, 0 ≤ C → C ≤ Real.sqrt (n : ℝ)/4 →
      (2 : ℝ)^(-(n : ℝ)/2+1/2+(211/192)*C^2+(14/3)*C+49/3+
          C*Real.log (2*(n : ℝ))/Real.log 2+K*Real.log ((n : ℝ)+2)) ≤
        (2 : ℝ)^(-(n : ℝ)/4) := by
  filter_upwards [eventually_small_support_exponent_le K hK] with n hn
  intro C hC hCN
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (hn C hC hCN)

end SymmetricSubgroupAsymptotics.BinaryMixtureNumerics
