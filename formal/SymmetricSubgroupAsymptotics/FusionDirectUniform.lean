import SymmetricSubgroupAsymptotics.FusionDirectDecay

/-! Uniform first-moment coefficients with the quadratic width loss
retained. The original factorial pointing, normalizer divisor and both
parity coefficients are inherited from the exact benchmark ratio.

These pointwise estimates do not assert a bound on a varying menu, an
actual physical cover, or the total subgroup sequence. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

private theorem fusionDirectKernel_pointing_identity (b h r : ℕ) (hr : r≤h)
    (D a e : ℝ) :
    fusionDirectKernel b h (2*r) D a e =
      (((b+2*r).factorial : ℝ)/(b.factorial : ℝ)) *
        fusionPointingRatio (b+2*r) (h-r) * (D/a) *
          (2 : ℝ)^(((((2*h : ℕ) : ℝ)-((2*r : ℕ) : ℝ)-16*e)/8)*(b : ℝ)) := by
  have hn : b+2*r+2*(h-r) = b+2*h := by omega
  have hm : ((b+2*r).factorial : ℝ) ≠ 0 := by positivity
  unfold fusionDirectKernel fusionNormalizedPointing fusionLocalFactor fusionPointingRatio
  rw [hn]
  field_simp

/-- The exact quadratic difference of the original and graph widths is
retained. The polynomial degree is `h+r+1`, and `D/a` remains the original
lift constant divided by the original physical action divisor. This is
valid for every complement degree and even for arbitrary real `e`. -/
theorem fusionDirectKernel_le_uniform (b h r : ℕ) (hr : r≤h)
    {D a e : ℝ} (hD : 0≤D) (ha : 0<a) :
    fusionDirectKernel b h (2*r) D a e ≤
      (eulerProduct⁻¹^2*(D/a)) * ((b+2*h+1 : ℕ) : ℝ)^(h+r+1) *
        (2 : ℝ)^(-2*e*(b : ℝ)-((h : ℝ)^2-(r : ℝ)^2)/4+
          ((h : ℝ)-(r : ℝ)+1)/4) := by
  have hn : b+2*r+2*(h-r) = b+2*h := by omega
  have hpoint := fusionPointingRatio_le (b+2*r) (h-r)
  rw [hn] at hpoint
  have hpoly :
      ((b+2*r : ℕ) : ℝ)^(2*r)*((b+2*h+1 : ℕ) : ℝ)^(h-r+1) ≤
        ((b+2*h+1 : ℕ) : ℝ)^(h+r+1) := by
    have hbase : ((b+2*r : ℕ) : ℝ) ≤ ((b+2*h+1 : ℕ) : ℝ) := by
      exact_mod_cast (show b+2*r≤b+2*h+1 by omega)
    calc
      _ ≤ ((b+2*h+1 : ℕ) : ℝ)^(2*r)*
          ((b+2*h+1 : ℕ) : ℝ)^(h-r+1) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase (2*r))
          (by positivity)
      _ = _ := by
        rw [← pow_add]
        congr 1
        omega
  have hexp :
      (((h-r : ℕ) : ℝ)+1)/4 +
        (-((h-r : ℕ) : ℝ)*((b+2*r : ℕ) : ℝ)/4-((h-r : ℕ) : ℝ)^2/4) +
          ((((2*h : ℕ) : ℝ)-((2*r : ℕ) : ℝ)-16*e)/8)*(b : ℝ) =
        -2*e*(b : ℝ)-((h : ℝ)^2-(r : ℝ)^2)/4+
          ((h : ℝ)-(r : ℝ)+1)/4 := by
    push_cast [Nat.cast_sub hr]
    ring
  calc
    _ = (((b+2*r).factorial : ℝ)/(b.factorial : ℝ)) *
        fusionPointingRatio (b+2*r) (h-r) * (D/a) *
          (2 : ℝ)^(((((2*h : ℕ) : ℝ)-((2*r : ℕ) : ℝ)-16*e)/8)*(b : ℝ)) :=
      fusionDirectKernel_pointing_identity b h r hr D a e
    _ ≤ ((b+2*r : ℕ) : ℝ)^(2*r) *
        ((eulerProduct⁻¹^2*(2 : ℝ)^((((h-r : ℕ) : ℝ)+1)/4)) *
          ((b+2*h+1 : ℕ) : ℝ)^(h-r+1) *
            (2 : ℝ)^(-((h-r : ℕ) : ℝ)*((b+2*r : ℕ) : ℝ)/4-
              ((h-r : ℕ) : ℝ)^2/4)) * (D/a) *
          (2 : ℝ)^(((((2*h : ℕ) : ℝ)-((2*r : ℕ) : ℝ)-16*e)/8)*(b : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (div_nonneg hD ha.le)
      exact mul_le_mul (fusion_factorial_ratio_le b (2*r)) hpoint
        (fusionPointingRatio_nonneg _ _) (by positivity)
    _ = (eulerProduct⁻¹^2*(D/a)) *
        (((b+2*r : ℕ) : ℝ)^(2*r)*((b+2*h+1 : ℕ) : ℝ)^(h-r+1)) *
          (2 : ℝ)^(-2*e*(b : ℝ)-((h : ℝ)^2-(r : ℝ)^2)/4+
            ((h : ℝ)-(r : ℝ)+1)/4) := by
      rw [← hexp, Real.rpow_add (by norm_num : (0 : ℝ)<2),
        Real.rpow_add (by norm_num : (0 : ℝ)<2)]
      ring
    _ ≤ _ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpoly (by positivity)) (by positivity)

/-- Numerical wide-prefix specialization. In physical-width notation
`w=2*h`, `v=2*r`, the assumptions are `v≤13*w/16` and `16*e≥w/32`.
No uniform bound on the number or total weight of entries is asserted. -/
theorem fusionDirectKernel_le_wide (b h r : ℕ) (hprefix : 16*r≤13*h)
    {D a e : ℝ} (hD : 0≤D) (ha : 0<a)
    (hgap : ((2*h : ℕ) : ℝ)/32≤16*e) :
    fusionDirectKernel b h (2*r) D a e ≤
      (eulerProduct⁻¹^2*(D/a)) * ((b+2*h+1 : ℕ) : ℝ)^(h+r+1) *
        (2 : ℝ)^(-((2*h : ℕ) : ℝ)*(b : ℝ)/256-
          87*((2*h : ℕ) : ℝ)^2/4096+((2*h : ℕ) : ℝ)/8+1/4) := by
  have hr : r≤h := by omega
  have hp : 16*(r : ℝ)≤13*(h : ℝ) := by exact_mod_cast hprefix
  have hsquare : 256*(r : ℝ)^2≤169*(h : ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp)
      (show 0≤13*(h : ℝ)+16*(r : ℝ) by positivity)]
  have hg : (h : ℝ)≤256*e := by
    push_cast at hgap
    linarith
  have hlinear : -2*e*(b : ℝ)≤-(h : ℝ)*(b : ℝ)/128 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hg) (Nat.cast_nonneg (α := ℝ) b)]
  apply (fusionDirectKernel_le_uniform b h r hr hD ha).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) r]

end SymmetricSubgroupAsymptotics
