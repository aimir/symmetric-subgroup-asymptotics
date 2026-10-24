import SymmetricSubgroupAsymptotics.TraceyElementarySharperLogBudget

/-! A uniform PRIMARY-SWITCH estimate in small affine dimensions. The
literal exponent threshold is proved arithmetically, not used as an
assumed frontier. Other endpoint, coefficient and actual top-ceiling
charges are deliberately not declared paid by this separate estimate. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryAffineDominantPrimeSwitchNumerics

def rate (q a : ℕ) : ℝ := Real.sqrt (2/(3*((q : ℝ)-1)*a))

theorem logb_nat_le_sub_one (q : ℕ) (hq : 2 ≤ q) :
    Real.logb 2 (q : ℝ) ≤ (q : ℝ)-1 := by
  have hnat := TraceyElementaryLogBudget.succ_le_two_pow (q-1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ q)] at hnat
  have hpow : (q : ℝ) ≤ (2 : ℝ)^(q-1) := by exact_mod_cast hnat
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast (show 0 < q by omega)) hpow
  rw [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] at hl
  simpa only [Nat.cast_sub (by omega : 1 ≤ q),Nat.cast_one] using hl

theorem primary_switch_le (q a : ℕ) (hq : 2 ≤ q) (ha : 512 ≤ a)
    (d : ℝ) (hd0 : 0 ≤ d) (hd6 : d ≤ 6) :
    rate q a * Real.sqrt (d+(a : ℝ)*Real.logb 2 (q : ℝ)+8/(rate q a)) ≤ 99/100 := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have haR : (512 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < a := by linarith
  have hprod : (512 : ℝ) ≤ ((q : ℝ)-1)*a := by
    have hh := mul_le_mul (by linarith : (1 : ℝ) ≤ (q : ℝ)-1) haR
      (by norm_num : (0 : ℝ) ≤ 512) (by linarith : (0 : ℝ) ≤ (q : ℝ)-1)
    simpa only [one_mul] using hh
  have hden : 0 < 3*((q : ℝ)-1)*a :=
    mul_pos (mul_pos (by norm_num) (by linarith)) ha0
  have hden_large : (1536 : ℝ) ≤ 3*((q : ℝ)-1)*a := by nlinarith only [hprod]
  have hu : 0 < rate q a := Real.sqrt_pos.mpr (div_pos (by norm_num) hden)
  have hu2 : (rate q a)^2 = 2/(3*((q : ℝ)-1)*a) :=
    Real.sq_sqrt (div_nonneg (by norm_num) hden.le)
  have husq : (rate q a)^2 ≤ 1/768 := by
    rw [hu2]
    exact (div_le_iff₀ hden).mpr (by nlinarith only [hden_large])
  have hule : rate q a ≤ 1/27 :=
    (sq_le_sq₀ hu.le (by norm_num : (0 : ℝ) ≤ 1/27)).mp (by nlinarith only [husq])
  have hlog := logb_nat_le_sub_one q hq
  have hlog0 : 0 ≤ Real.logb 2 (q : ℝ) :=
    (Real.logb_pos (by norm_num : (1 : ℝ) < 2) (by linarith : (1 : ℝ) < q)).le
  have hbase : (rate q a)^2*((a : ℝ)*Real.logb 2 (q : ℝ)) ≤ 2/3 := by
    rw [hu2,div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    have hh := mul_le_mul_of_nonneg_left hlog ha0.le
    nlinarith only [hh]
  have hdim : (rate q a)^2*d ≤ (1/768 : ℝ)*6 :=
    mul_le_mul husq hd6 hd0 (by norm_num)
  have hrad : 0 ≤ d+(a : ℝ)*Real.logb 2 (q : ℝ)+8/(rate q a) :=
    add_nonneg (add_nonneg hd0 (mul_nonneg ha0.le hlog0))
      (div_nonneg (by norm_num) hu.le)
  have hexpand :
      (rate q a * Real.sqrt (d+(a : ℝ)*Real.logb 2 (q : ℝ)+8/(rate q a)))^2 =
        (rate q a)^2*d+(rate q a)^2*((a : ℝ)*Real.logb 2 (q : ℝ))+8*rate q a := by
    rw [mul_pow,Real.sq_sqrt hrad]
    field_simp [hu.ne'] <;> ring
  apply (sq_le_sq₀ (mul_nonneg hu.le (Real.sqrt_nonneg _))
    (by norm_num : (0 : ℝ) ≤ 99/100)).mp
  rw [hexpand]
  nlinarith only [hdim,hbase,hule]

end SymmetricSubgroupAsymptotics.BinaryAffineDominantPrimeSwitchNumerics
