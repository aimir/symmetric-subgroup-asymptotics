import SymmetricSubgroupAsymptotics.FusionArbitraryWidth
import SymmetricSubgroupAsymptotics.FusionHotBenchmark

/-!
# Uniform arbitrary-width benchmark normalization

The fixed-width continuation bound deliberately discarded the quadratic loss
in the removed width.  Growing action menus need that reserve.  This file
retains it while keeping the exact odd-parity coefficient and the original
factorial normalization.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- Uniform normalization with the quadratic removed-width reserve retained.
For `r = floor (w/2)`, the exponent is
`-r*b/4-r^2/4+r/4+1/4`. -/
theorem fusionWidthPointingRatio_quadratic_le (b w : ℕ) :
    fusionWidthPointingRatio b w ≤
      eulerProduct⁻¹ ^ 2 * ((b + w + 1 : ℕ) : ℝ) ^ (w + 2) *
        (2 : ℝ) ^ (-(halfDegree w : ℝ) * b / 4 -
          (halfDegree w : ℝ) ^ 2 / 4 + (halfDegree w : ℝ) / 4 + 1 / 4) := by
  let k := halfDegree b
  let t := halfDegree (b + w) - k
  let r := halfDegree w
  have hkt : k + t = halfDegree (b + w) := by
    dsimp [k, t, halfDegree]
    omega
  have htw : t ≤ w := by
    dsimp [t, k, halfDegree]
    omega
  have hrt : r ≤ t := by
    dsimp [r, t, k, halfDegree]
    omega
  have hkb : b ≤ 2 * k + 1 := by
    dsimp [k, halfDegree]
    omega
  have hkn : 2 * (k + t) ≤ b + w := by
    rw [hkt]
    unfold halfDegree
    omega
  have hcoefpos :
      0 < (analyticParityCoefficient (parity (b + w)) (k + t) : ℝ) := by
    exact_mod_cast analyticParityCoefficient_positive (parity (b + w)) (k + t)
  have hcoef :
      (analyticParityCoefficient (parity b) k : ℝ) /
          analyticParityCoefficient (parity (b + w)) (k + t) ≤
        ((k : ℝ) + 1) * (2 * ((k + t : ℕ) : ℝ)) ^ t := by
    apply (div_le_iff₀ hcoefpos).mpr
    exact_mod_cast
      analyticParityCoefficient_cross_shift (parity b) (parity (b + w)) k t
  have hpoly :
      ((k : ℝ) + 1) ^ 2 * (2 * ((k + t : ℕ) : ℝ)) ^ t ≤
        ((b + w + 1 : ℕ) : ℝ) ^ (w + 2) := by
    have hk : (k : ℝ) + 1 ≤ ((b + w + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show k + 1 ≤ b + w + 1 by omega)
    have hn : 2 * ((k + t : ℕ) : ℝ) ≤ ((b + w + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 * (k + t) ≤ b + w + 1 by omega)
    have h1 : (1 : ℝ) ≤ ((b + w + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ b + w + 1 by omega)
    calc
      _ ≤ ((b + w + 1 : ℕ) : ℝ) ^ 2 *
          ((b + w + 1 : ℕ) : ℝ) ^ t :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hk 2)
          (pow_le_pow_left₀ (by positivity) hn t) (by positivity) (by positivity)
      _ = ((b + w + 1 : ℕ) : ℝ) ^ (t + 2) := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ _ := pow_le_pow_right₀ h1 (by omega)
  have hexp :
      -(t : ℝ) * k / 2 - (t : ℝ) ^ 2 / 4 + 1 / 4 ≤
        -(r : ℝ) * b / 4 - (r : ℝ) ^ 2 / 4 + (r : ℝ) / 4 + 1 / 4 := by
    have hrtR : (r : ℝ) ≤ (t : ℝ) := by exact_mod_cast hrt
    have hkbR : (b : ℝ) ≤ 2 * (k : ℝ) + 1 := by exact_mod_cast hkb
    have hk0 : 0 ≤ (k : ℝ) := by positivity
    have hr0 : 0 ≤ (r : ℝ) := by positivity
    have ht0 : 0 ≤ (t : ℝ) := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hrtR) hk0,
      mul_nonneg (sub_nonneg.mpr hrtR) (add_nonneg ht0 hr0),
      mul_nonneg hr0 (sub_nonneg.mpr hkbR)]
  rw [fusionWidthPointingRatio_eq, ← hkt]
  change
    ((binaryGaussianSum k : ℝ) / binaryGaussianSum (k + t)) *
        ((analyticParityCoefficient (parity b) k : ℝ) /
          analyticParityCoefficient (parity (b + w)) (k + t)) ≤ _
  calc
    _ ≤ (eulerProduct⁻¹ ^ 2 * ((k : ℝ) + 1) *
          (2 : ℝ) ^ (-(t : ℝ) * k / 2 - (t : ℝ) ^ 2 / 4 + 1 / 4)) *
        (((k : ℝ) + 1) * (2 * ((k + t : ℕ) : ℝ)) ^ t) := by
      apply mul_le_mul (fusionGaussianRatio_le k t) hcoef
      · exact div_nonneg
          (by exact_mod_cast (analyticParityCoefficient_positive _ _).le)
          hcoefpos.le
      · positivity
    _ = eulerProduct⁻¹ ^ 2 *
        (((k : ℝ) + 1) ^ 2 * (2 * ((k + t : ℕ) : ℝ)) ^ t) *
          (2 : ℝ) ^ (-(t : ℝ) * k / 2 - (t : ℝ) ^ 2 / 4 + 1 / 4) := by
      ring
    _ ≤ eulerProduct⁻¹ ^ 2 * ((b + w + 1 : ℕ) : ℝ) ^ (w + 2) *
        (2 : ℝ) ^ (-(r : ℝ) * b / 4 - (r : ℝ) ^ 2 / 4 +
          (r : ℝ) / 4 + 1 / 4) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpoly (by positivity))
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
        (by positivity) (by positivity)
    _ = _ := by rfl

/-- The arbitrary-width cold kernel with the removed-width quadratic reserve
still visible.  This is the pointwise form needed before summing a growing
menu of actions: the original divisor `a`, multiplicity `D`, and local
capacity exponent `α * b` are all retained. -/
theorem fusionWidthColdKernel_quadratic_le (b w : ℕ) {D a α : ℝ}
    (hD : 0 ≤ D) (ha : 0 < a) :
    fusionWidthColdKernel b w D a α ≤
      eulerProduct⁻¹ ^ 2 * ((b + w + 1 : ℕ) : ℝ) ^ (w + 2) * (D / a) *
        (2 : ℝ) ^ (-(halfDegree w : ℝ) * b / 4 -
          (halfDegree w : ℝ) ^ 2 / 4 + (halfDegree w : ℝ) / 4 + 1 / 4 +
          α * b) := by
  unfold fusionWidthColdKernel
  calc
    _ ≤ (eulerProduct⁻¹ ^ 2 * ((b + w + 1 : ℕ) : ℝ) ^ (w + 2) *
          (2 : ℝ) ^ (-(halfDegree w : ℝ) * b / 4 -
            (halfDegree w : ℝ) ^ 2 / 4 + (halfDegree w : ℝ) / 4 + 1 / 4)) *
        (D / a) * (2 : ℝ) ^ (α * b) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (fusionWidthPointingRatio_quadratic_le b w)
          (div_nonneg hD ha.le)) (by positivity)
    _ = (eulerProduct⁻¹ ^ 2 * ((b + w + 1 : ℕ) : ℝ) ^ (w + 2) *
          (D / a)) *
        ((2 : ℝ) ^ (-(halfDegree w : ℝ) * b / 4 -
          (halfDegree w : ℝ) ^ 2 / 4 + (halfDegree w : ℝ) / 4 + 1 / 4) *
          (2 : ℝ) ^ (α * b)) := by ring
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]

/-- A factorial is bounded by the corresponding power of its successor.
This elementary form is sufficient for the uniform hot normalization. -/
theorem factorial_le_succ_pow (n : ℕ) :
    n.factorial ≤ (n + 1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.factorial_succ]
      calc
        (n + 1) * n.factorial ≤ (n + 1) * (n + 1) ^ n :=
          Nat.mul_le_mul_left (n + 1) ih
        _ = (n + 1) ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]
        _ ≤ (n + 2) ^ (n + 1) := Nat.pow_le_pow_left (by omega) _

/-- Hot-pointing normalization at arbitrary removed width.  No relation
between the complement degree and removed width is required; the resulting
factorial loss is kept as one explicit power of the ambient degree. -/
theorem fusionWidthHot_pointing_denominator_le (b w : ℕ) :
    (((b + w).factorial : ℝ) / (b.factorial : ℝ)) /
        exactBenchmark (b + w) ≤
      eulerProduct⁻¹ * (((b + w + 1 : ℕ) : ℝ) ^ (b + w)) *
        (2 : ℝ) ^ (-((b + w : ℕ) : ℝ) ^ 2 / 16 +
          5 * ((b + w : ℕ) : ℝ) / 8 + 1 / 4) := by
  let n := b + w
  let r := halfDegree n
  have hrn : r ≤ n := by
    dsimp [r, halfDegree]
    omega
  have hrn2 : 2 * r ≤ n := by
    dsimp [r, halfDegree]
    omega
  have hnr : n ≤ 2 * r + 1 := by
    dsimp [r, halfDegree]
    omega
  have hφ := euler_positive
  have hc := parityCoefficient_linear_lower n
  have hG := fusionGaussianSum_lower r
  have hfacNat : r.factorial ≤ (n + 1) ^ n :=
    (Nat.factorial_le hrn).trans (factorial_le_succ_pow n)
  have hfac : (r.factorial : ℝ) / (b.factorial : ℝ) ≤
      (((n + 1 : ℕ) : ℝ) ^ n) := by
    have hb1 : (1 : ℝ) ≤ (b.factorial : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos b)
    have hfr : (r.factorial : ℝ) ≤ (((n + 1 : ℕ) : ℝ) ^ n) := by
      exact_mod_cast hfacNat
    have hbpos : (0 : ℝ) < (b.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos b
    have hpow0 : 0 ≤ (((n + 1 : ℕ) : ℝ) ^ n) := by positivity
    apply (div_le_iff₀ hbpos).mpr
    exact hfr.trans (le_mul_of_one_le_right hpow0 hb1)
  have hden :
      eulerProduct * (2 : ℝ) ^ ((r : ℝ) ^ 2 / 4 - (r : ℝ) - 1 / 4) *
          ((b.factorial : ℝ) / (r.factorial : ℝ)) ≤
        (b.factorial : ℝ) * (binaryGaussianSum r : ℝ) *
          (parityCoefficient n : ℝ) := by
    have hc0 : 0 ≤
        1 / ((2 : ℝ) ^ halfDegree n * (halfDegree n).factorial) := by positivity
    have hG0 : 0 ≤ (binaryGaussianSum r : ℝ) := by
      exact_mod_cast (binaryGaussianSum_pos r).le
    have hprod := mul_le_mul hG hc hc0 hG0
    calc
      _ = (b.factorial : ℝ) *
          ((eulerProduct * (2 : ℝ) ^ ((r : ℝ) ^ 2 / 4 - 1 / 4)) *
            (1 / ((2 : ℝ) ^ r * (r.factorial : ℝ)))) := by
        rw [← Real.rpow_natCast]
        rw [div_eq_mul_inv]
        field_simp
        simp only [← Real.rpow_natCast]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 2
        ring
      _ ≤ (b.factorial : ℝ) *
          ((binaryGaussianSum r : ℝ) * (parityCoefficient n : ℝ)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = _ := by ring
  have hexp :
      -((r : ℝ) ^ 2 / 4 - (r : ℝ) - 1 / 4) ≤
        -((n : ℝ) ^ 2) / 16 + 5 * (n : ℝ) / 8 + 1 / 4 := by
    have hnrR : (n : ℝ) ≤ 2 * (r : ℝ) + 1 := by exact_mod_cast hnr
    have hrnR : 2 * (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hrn2
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    have hr0 : 0 ≤ (r : ℝ) := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hnrR)
      (show 0 ≤ (n : ℝ) + 2 * r by positivity)]
  calc
    _ = 1 / ((b.factorial : ℝ) * (binaryGaussianSum r : ℝ) *
        (parityCoefficient n : ℝ)) := by
      dsimp [exactBenchmark, n, r]
      field_simp
    _ ≤ 1 / (eulerProduct *
          (2 : ℝ) ^ ((r : ℝ) ^ 2 / 4 - (r : ℝ) - 1 / 4) *
            ((b.factorial : ℝ) / (r.factorial : ℝ))) :=
      one_div_le_one_div_of_le (by positivity) hden
    _ = ((r.factorial : ℝ) / (b.factorial : ℝ)) * eulerProduct⁻¹ *
        (2 : ℝ) ^ (-((r : ℝ) ^ 2 / 4 - (r : ℝ) - 1 / 4)) := by
      rw [one_div, mul_inv_rev, mul_inv_rev,
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
    _ ≤ (((n + 1 : ℕ) : ℝ) ^ n) * eulerProduct⁻¹ *
        (2 : ℝ) ^ (-((r : ℝ) ^ 2 / 4 - (r : ℝ) - 1 / 4)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hfac (inv_nonneg.mpr hφ.le)) (by positivity)
    _ ≤ (((n + 1 : ℕ) : ℝ) ^ n) * eulerProduct⁻¹ *
        (2 : ℝ) ^ (-((n : ℝ) ^ 2) / 16 + 5 * (n : ℝ) / 8 + 1 / 4) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) (by positivity)
    _ = _ := by
      dsimp [n]
      ring

end SymmetricSubgroupAsymptotics

end
