import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate
import SymmetricSubgroupAsymptotics.TraceyAffineInducedModuleInput
import Mathlib.Tactic.FieldSimp

/-! Calculus-free monotonicity of the coarse permutation ceiling above2.
This is scalar arithmetic, not a published permutation-generator input.
The proof uses the actual logarithm and retains ceiling rounding. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TraceyCoarseCeilingMonotonicity

/-- The logarithmic square-root quotient increases for real arguments>=2. -/
theorem quotient_mono {x y : ℝ} (hx2 : 2 ≤ x) (hxy : x ≤ y) :
    x/Real.sqrt (Real.logb 2 x) ≤ y/Real.sqrt (Real.logb 2 y) := by
  have hx : 0 < x := by linarith only [hx2]
  have hy : 0 < y := hx.trans_le hxy
  have hlogLower := Real.one_sub_inv_le_log_of_pos hx
  have hinv : x⁻¹ ≤ (1/2 : ℝ) := by
    rw [←one_div]
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hx2
  have hlogHalf : (1/2 : ℝ) ≤ Real.log x := by linarith only [hlogLower,hinv]
  have hratio := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at hratio
  have hlogMul : x*(Real.log y-Real.log x) ≤ y-x := by
    calc
      x*(Real.log y-Real.log x) ≤ x*(y/x-1) := mul_le_mul_of_nonneg_left hratio hx.le
      _ = y-x := by field_simp
  have hdiff : 0 ≤ y^2-x^2 := sub_nonneg.mpr ((sq_le_sq₀ hx.le hy.le).mpr hxy)
  have hpositive := mul_nonneg hdiff (show 0 ≤ Real.log x-1/2 by linarith only [hlogHalf])
  have hcross : x^2*Real.log y ≤ y^2*Real.log x := by
    have hh := mul_le_mul_of_nonneg_left hlogMul hx.le
    nlinarith only [hh,hpositive,sq_nonneg (y-x)]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbase : x^2*Real.logb 2 y ≤ y^2*Real.logb 2 x := by
    have hh := div_le_div_of_nonneg_right hcross hlog2.le
    simpa only [Real.logb,mul_div_assoc] using hh
  have hlx : 0 < Real.logb 2 x := Real.logb_pos (by norm_num) (by linarith only [hx2])
  have hly : 0 < Real.logb 2 y := Real.logb_pos (by norm_num) (by linarith only [hx2,hxy])
  have hsx : 0 < Real.sqrt (Real.logb 2 x) := Real.sqrt_pos.mpr hlx
  have hsy : 0 < Real.sqrt (Real.logb 2 y) := Real.sqrt_pos.mpr hly
  apply (div_le_div_iff₀ hsx hsy).mpr
  apply (sq_le_sq₀ (mul_nonneg hx.le hsy.le) (mul_nonneg hy.le hsx.le)).mp
  simpa only [mul_pow,Real.sq_sqrt hlx.le,Real.sq_sqrt hly.le] using hbase

/-- Integer ceiling rounding preserves this monotonicity. -/
theorem ceiling_mono {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    traceyPermutationGeneratorCeiling m ≤ traceyPermutationGeneratorCeiling n := by
  apply Nat.ceil_mono
  exact quotient_mono (by exact_mod_cast hm) (by exact_mod_cast hmn)

end SymmetricSubgroupAsymptotics.TraceyCoarseCeilingMonotonicity
