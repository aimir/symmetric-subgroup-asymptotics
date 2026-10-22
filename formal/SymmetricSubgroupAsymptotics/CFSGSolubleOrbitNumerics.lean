import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorNumerics

/-! The same orbit potential pays a quadratic logarithmic local cost.
This allows the asymptotic soluble recurrence to avoid both sharp primitive
inputs. The scalar constant is intentionally loose. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSolubleOrbitNumerics
open LargeOrbitGeneratorNumerics

theorem sqrt_quadratic_le_binary_exp (a : ℝ) (ha : 0 ≤ a) :
    Real.sqrt (1+a) * (1+(a^2+a)/256) ≤ (2:ℝ)^a := by
  have hs : Real.sqrt (1+a) ≤ Real.exp (a/2) := by
    rw [Real.exp_half]
    exact Real.sqrt_le_sqrt (by linarith [Real.add_one_le_exp a])
  have hp : 1+(a^2+a)/256 ≤ Real.exp (a/8) := by
    have he := Real.add_one_le_exp (a/16)
    have hsq : (1+a/16)^2 ≤ (Real.exp (a/16))^2 :=
      by simpa only [add_comm (a/16) 1] using pow_le_pow_left₀ (by positivity : 0 ≤ a/16+1) he 2
    have heq : (Real.exp (a/16))^2 = Real.exp (a/8) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [heq] at hsq
    nlinarith
  calc
    _ ≤ Real.exp (a/2) * Real.exp (a/8) :=
      mul_le_mul hs hp (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (5*a/8) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (Real.log 2*a) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.log_two_gt_d9]
    _ = _ := (Real.rpow_def_of_pos (by norm_num) _).symm

theorem normalized_block (a b : ℝ) (ha : 0 ≤ a) (hb : 1 ≤ b) :
    (5*(a^2+a)+1280) * Real.sqrt (a+b) ≤
      1280*(2:ℝ)^a * Real.sqrt b := by
  have hs : Real.sqrt (a+b) ≤ Real.sqrt b * Real.sqrt (1+a) := by
    rw [← Real.sqrt_mul (by linarith : 0 ≤ b)]
    apply Real.sqrt_le_sqrt
    nlinarith
  calc
    _ ≤ (1280*(1+(a^2+a)/256)) * (Real.sqrt b * Real.sqrt (1+a)) := by
      apply mul_le_mul _ hs (Real.sqrt_nonneg _) (by positivity)
      ring_nf
      exact le_rfl
    _ = (1280*Real.sqrt b) * (Real.sqrt (1+a)*(1+(a^2+a)/256)) := by ring
    _ ≤ (1280*Real.sqrt b)*(2:ℝ)^a :=
      mul_le_mul_of_nonneg_left (sqrt_quadratic_le_binary_exp a ha) (by positivity)
    _ = _ := by ring

theorem primitive_recurrence (r : ℕ) (hr : 2 ≤ r) :
    (Real.logb 2 r)^2+Real.logb 2 r ≤
      1280*r/Real.sqrt (Real.logb 2 r) := by
  let a := Real.logb 2 r
  have ha : 1 ≤ a := by
    dsimp [a]
    rw [← Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast hr)
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr (by linarith)
  apply (le_div_iff₀ hs).mpr
  have h := normalized_block a 1 (by linarith) le_rfl
  simp only [Real.sqrt_one, mul_one] at h
  have hp : (2:ℝ)^a = r := Real.rpow_logb (by norm_num) (by norm_num) (by exact_mod_cast (by omega : 0<r))
  rw [hp] at h
  exact (mul_le_mul (by nlinarith : a^2+a ≤ 5*(a^2+a)+1280)
    (Real.sqrt_le_sqrt (by linarith : a ≤ a+1)) (Real.sqrt_nonneg _) (by positivity)).trans h

theorem block_recurrence (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) :
    (traceyInducedGeneratorCeiling 1 s : ℝ)*((Real.logb 2 r)^2+Real.logb 2 r) +
      1280*s/Real.sqrt (Real.logb 2 s) ≤
        1280*(r*s:ℕ)/Real.sqrt (Real.logb 2 (r*s:ℕ)) := by
  let a := Real.logb 2 r
  let b := Real.logb 2 s
  have hrR : (2:ℝ) ≤ r := by exact_mod_cast hr
  have hsR : (2:ℝ) ≤ s := by exact_mod_cast hs
  have ha : 1 ≤ a := by
    dsimp [a]
    rw [← Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) hrR
  have hb : 1 ≤ b := by
    dsimp [b]
    rw [← Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) hsR
  have hbpos : 0 < Real.sqrt b := Real.sqrt_pos.mpr (by linarith)
  have habpos : 0 < Real.sqrt (a+b) := Real.sqrt_pos.mpr (by linarith)
  have hnum := normalized_block a b (by linarith) hb
  have hpow : (2:ℝ)^a = r := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
  rw [hpow] at hnum
  have hscaled : (5*(a^2+a)+1280)*(s:ℝ)/Real.sqrt b ≤ 1280*r*s/Real.sqrt (a+b) := by
    rw [div_le_div_iff₀ hbpos habpos]
    nlinarith [mul_le_mul_of_nonneg_right hnum (show (0 : ℝ) ≤ s from Nat.cast_nonneg s)]
  have hB := induced_ceiling_le_five s hs
  have hmul := mul_le_mul_of_nonneg_right hB (show 0 ≤ a^2+a from by positivity)
  change (traceyInducedGeneratorCeiling 1 s:ℝ)*(a^2+a) ≤ (5*s/Real.sqrt b)*(a^2+a) at hmul
  have heq : (5*(s:ℝ)/Real.sqrt b)*(a^2+a)+1280*s/Real.sqrt b =
      (5*(a^2+a)+1280)*s/Real.sqrt b := by ring
  have hfirst : (traceyInducedGeneratorCeiling 1 s:ℝ)*(a^2+a)+1280*s/Real.sqrt b ≤
      (5*(a^2+a)+1280)*s/Real.sqrt b := by rw [← heq]; linarith [hmul]
  have hlog : Real.logb 2 (r*s:ℕ) = a+b := by
    rw [Nat.cast_mul, Real.logb_mul (by linarith : (r:ℝ)≠0) (by linarith : (s:ℝ)≠0)]
  rw [hlog, Nat.cast_mul]
  simpa only [mul_assoc] using hfirst.trans hscaled

end SymmetricSubgroupAsymptotics.CFSGSolubleOrbitNumerics
