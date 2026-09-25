import SymmetricSubgroupAsymptotics.SaddleEstimates

/-!
# First corrections for the exact positive saddle

The logarithmic estimates keep the exact radius and bound the errors by an
explicit multiple of the inverse square of its leading fourth-root scale.
-/

set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics

private theorem log_one_sub_quadratic {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1 / 2) :
    |Real.log (1 - u) + u + u ^ 2 / 2| ≤ 2 * u ^ 3 := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |u| < 1 by rw [abs_of_nonneg hu]; linarith) 2
  norm_num [Finset.sum_range_succ, abs_of_nonneg hu] at h
  have hb : u ^ 3 / (1 - u) ≤ 2 * u ^ 3 := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - u)).mpr
    nlinarith [mul_nonneg (pow_nonneg hu 3) (show 0 ≤ 1 - 2 * u by linarith)]
  calc
    |Real.log (1 - u) + u + u ^ 2 / 2| = |u + u ^ 2 / 2 + Real.log (1-u)| := by congr 1; ring
    _ ≤ u ^ 3 / (1-u) := h
    _ ≤ 2 * u ^ 3 := hb

private theorem log_one_add_linear {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |Real.log (1 + u) - u| ≤ 2 * u ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |-u| < 1 by rw [abs_neg]; linarith) 1
  norm_num [Finset.sum_range_succ, abs_neg, sq_abs] at h
  have hb : u ^ 2 / (1 - |u|) ≤ 2 * u ^ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - |u|)).mpr
    nlinarith [mul_nonneg (sq_nonneg u) (show 0 ≤ 1 - 2 * |u| by linarith)]
  calc
    |Real.log (1 + u) - u| = |-u + Real.log (1 + u)| := by congr 1; ring
    _ ≤ u ^ 2 / (1 - |u|) := h
    _ ≤ 2 * u ^ 2 := hb

theorem saddleVariance_log_error_explicit (r : ℕ) (hr : 0 < r) :
    |Real.log (saddleVariance (saddleRadius r)) - Real.log (4 * (r : ℝ))| ≤
      208 / saddleScale r ^ 2 := by
  let t := saddleVariance (saddleRadius r) / (4 * (r : ℝ))
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hb := saddleVariance_bounds r hr
  have ht0 : 0 < t := div_pos (saddleVariance_saddleRadius_pos r hr) (by positivity)
  have ht1 : t ≤ 1 := by dsimp [t]; apply (div_le_one (by positivity)).mpr; exact hb.2
  have ht4 : 1 / 4 ≤ t := by dsimp [t]; apply (le_div_iff₀ (by positivity)).mpr; linarith [hb.1]
  have hlog0 : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht1
  have hlog := Real.one_sub_inv_le_log_of_pos ht0
  have hinv : t⁻¹ - 1 ≤ 4 * (1 - t) := by
    rw [inv_eq_one_div]
    apply sub_le_iff_le_add.mpr
    rw [div_le_iff₀ ht0]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (show 0 ≤ 4*t-1 by linarith)]
  have he := saddleVariance_relative_error r hr
  change |t - 1| ≤ 52 / saddleScale r ^ 2 at he
  rw [abs_of_nonpos (sub_nonpos.mpr ht1)] at he
  have hid : Real.log (saddleVariance (saddleRadius r)) - Real.log (4 * (r : ℝ)) = Real.log t := by
    dsimp [t]
    rw [Real.log_div (saddleVariance_saddleRadius_pos r hr).ne' (by positivity)]
  rw [hid, abs_of_nonpos hlog0]
  calc
    -Real.log t ≤ 4 * (1-t) := by linarith
    _ ≤ 4 * (52 / saddleScale r ^ 2) := by linarith
    _ = 208 / saddleScale r ^ 2 := by ring

theorem saddleAmplitude_log_firstCorrection_explicit (r : ℕ) (hr : 683 ≤ r) :
    |Real.log (1 + saddleRadius r / 6) -
      (Real.log (saddleScale r / 6) + 6 / saddleScale r)| ≤
        152 / saddleScale r ^ 2 := by
  have hr0 : 0 < r := by omega
  let x := saddleScale r
  let ρ := saddleRadius r
  let u := (ρ - x + 6) / x
  have hx : 16 ≤ x := sixteen_le_saddleScale r hr
  have hx0 : 0 < x := saddleScale_pos r hr0
  have hρ : 0 < ρ := saddleRadius_pos r hr0
  have he := saddleRadius_scale_error r hr0
  change 0 ≤ x-ρ ∧ x-ρ ≤ 80/x at he
  have hd5 : x-ρ ≤ 5 := le_trans he.2 ((div_le_iff₀ hx0).mpr (by linarith))
  have hu0 : 0 ≤ u := div_nonneg (by linarith) hx0.le
  have hu6 : u ≤ 6/x := by dsimp [u]; gcongr; linarith [he.1]
  have hu : |u| ≤ 1/2 := by rw [abs_of_nonneg hu0]; exact hu6.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have ht := log_one_add_linear hu
  have hid : Real.log (1 + ρ / 6) = Real.log (x / 6) + Real.log (1 + u) := by
    rw [← Real.log_mul (by positivity : x/6 ≠ 0) (by positivity : 1+u ≠ 0)]
    congr 1
    dsimp [u]
    field_simp
    ring
  have he' : |u - 6/x| ≤ 80/x^2 := by
    have hd := div_le_div_of_nonneg_right he.2 hx0.le
    have hu' : u-6/x = -(x-ρ)/x := by dsimp [u]; ring
    rw [hu', abs_div, abs_neg, abs_of_nonneg he.1, abs_of_pos hx0]
    convert hd using 1; ring
  have hu2 : 2*u^2 ≤ 72/x^2 := by
    have hs := pow_le_pow_left₀ hu0 hu6 2
    calc
      2*u^2 ≤ 2*(6/x)^2 := by linarith
      _ = 72/x^2 := by ring
  change |Real.log (1+ρ/6) - (Real.log (x/6)+6/x)| ≤ 152/x^2
  rw [hid]
  calc
    |Real.log (x/6)+Real.log (1+u)-(Real.log (x/6)+6/x)| =
      |(Real.log (1+u)-u)+(u-6/x)| := by congr 1; ring
    _ ≤ |Real.log (1+u)-u|+|u-6/x| := abs_add_le _ _
    _ ≤ 72/x^2 + 80/x^2 := add_le_add (ht.trans hu2) he'
    _ = 152/x^2 := by ring

theorem saddleExponent_firstCorrection_explicit (r : ℕ) (hr : 683 ≤ r) :
    |(criticalPolynomial (saddleRadius r) - (r : ℝ) * Real.log (saddleRadius r)) -
      ((r : ℝ)/4 - (r : ℝ)*Real.log (saddleScale r) + saddleScale r ^ 2/6 +
        saddleScale r/2 - 4/3 - 4/saddleScale r)| ≤
      1000000 / saddleScale r ^ 2 := by
  have hr0 : 0 < r := by omega
  let x := saddleScale r
  let ρ := saddleRadius r
  let v := x * (x-ρ)
  let u := (x-ρ)/x
  let E := Real.log (1-u) + u + u^2/2
  have hx : 16 ≤ x := sixteen_le_saddleScale r hr
  have hx0 : 0 < x := saddleScale_pos r hr0
  have hρ : 0 < ρ := saddleRadius_pos r hr0
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hx4 : x^4 = 96*(r:ℝ) := saddleScale_pow_four r
  have he := saddleRadius_scale_error r hr0
  change 0 ≤ x-ρ ∧ x-ρ ≤ 80/x at he
  have hv0 : 0 ≤ v := mul_nonneg hx0.le he.1
  have hv80 : v ≤ 80 := by
    dsimp [v]
    have hh := (le_div_iff₀ hx0).mp he.2
    nlinarith only [hh]
  have hu0 : 0 ≤ u := div_nonneg he.1 hx0.le
  have huv : u = v/x^2 := by dsimp [u,v]; field_simp
  have hu : u ≤ 1/2 := by
    rw [huv]
    apply (div_le_iff₀ (sq_pos_of_pos hx0)).mpr
    nlinarith [sq_nonneg (x-16)]
  have hE : |E| ≤ 2*u^3 := log_one_sub_quadratic hu0 hu
  have hexp := saddleRadius_expansion r hr
  change |ρ - (x - 8/x - 12/x^2)| ≤ 2048/x^3 at hexp
  have hw : |x*(v-8)| ≤ 140 := by
    have hmul := mul_le_mul_of_nonneg_left hexp (sq_nonneg x)
    have hmul' : |x^2*(ρ-(x-8/x-12/x^2))| ≤ 2048/x := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg x)]
      convert hmul using 1; field_simp
    have hid : x*(v-8) = 12-x^2*(ρ-(x-8/x-12/x^2)) := by
      dsimp [v]
      field_simp
      ring
    rw [hid]
    calc
      |12-x^2*(ρ-(x-8/x-12/x^2))| ≤ |(12:ℝ)|+|x^2*(ρ-(x-8/x-12/x^2))| := abs_sub _ _
      _ ≤ 12+2048/x := add_le_add (by norm_num) hmul'
      _ ≤ 140 := by have hh : 2048/x ≤ 128 := (div_le_iff₀ hx0).mpr (by linarith); linarith
  have hw2 : (x*(v-8))^2 ≤ 19600 := by
    have hh := pow_le_pow_left₀ (abs_nonneg (x*(v-8))) hw 2
    simpa only [sq_abs, show (140:ℝ)^2 = 19600 by norm_num] using hh
  have hv2 : v^2 ≤ 6400 := by nlinarith
  have hv3 : v^3 ≤ 512000 := by
    have hh := pow_le_pow_left₀ hv0 hv80 3
    norm_num at hh
    exact hh
  have hv4 : v^4 ≤ 40960000 := by
    have hh := pow_le_pow_left₀ hv0 hv80 4
    norm_num at hh
    exact hh
  have hv4div : 0 ≤ v^4/(384*x^2) ∧ v^4/(384*x^2) ≤ 40960000/384 := by
    constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : 0 < 384*x^2)).mpr
      nlinarith [sq_nonneg (x-1)]
  have hEscale : |(r:ℝ)*x^2*E| ≤ 512000/48 := by
    calc
      |(r:ℝ)*x^2*E| = (r:ℝ)*x^2*|E| := by rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ (r:ℝ)*x^2*(2*u^3) := mul_le_mul_of_nonneg_left hE (by positivity)
      _ = v^3/48 := by
        rw [show (r:ℝ) = x^4/96 by linarith, huv]
        field_simp
        ring
      _ ≤ 512000/48 := by linarith
  have hlog : Real.log ρ = Real.log x + Real.log (1-u) := by
    have hprod : ρ = x*(1-u) := by dsimp [u]; field_simp; ring
    rw [hprod, Real.log_mul hx0.ne' (by linarith : 1-u ≠ 0)]
  let D := (criticalPolynomial ρ - (r:ℝ)*Real.log ρ) -
    ((r:ℝ)/4 - (r:ℝ)*Real.log x + x^2/6 + x/2 - 4/3 - 4/x)
  have hid : x^2*D = (x*(v-8))^2/48 - x*(v-8)/2 + v^2/6 - v^3/96 +
      v^4/(384*x^2) - (r:ℝ)*x^2*E := by
    dsimp [D, E]
    rw [hlog]
    have hrx : (r:ℝ) = x^4/96 := by linarith
    rw [hrx]
    dsimp [u,v,criticalPolynomial]
    field_simp
    ring
  have hbound : |x^2*D| ≤ 1000000 := by
    rw [hid]
    obtain ⟨hwlo,hwhi⟩ := abs_le.mp hw
    obtain ⟨hElo,hEhi⟩ := abs_le.mp hEscale
    apply abs_le.mpr
    constructor <;> nlinarith only [hwlo,hwhi,hElo,hEhi,hw2,hv2,hv3,hv4div.1,hv4div.2,
      sq_nonneg (x*(v-8)), sq_nonneg v, pow_nonneg hv0 3]
  change |D| ≤ 1000000/x^2
  apply (le_div_iff₀ (sq_pos_of_pos hx0)).mpr
  rw [abs_mul, abs_of_nonneg (sq_nonneg x)] at hbound
  nlinarith only [hbound]

/-- The logarithm of the complete saddle factor, uniformly for amplitudes
between the even and odd ones. The first correction is `(6 * ε - 4) / x`. -/
theorem saddleLog_firstCorrection_explicit (r : ℕ) (hr : 683 ≤ r)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    |(criticalPolynomial (saddleRadius r) - (r : ℝ) * Real.log (saddleRadius r) +
        ε * Real.log (1 + saddleRadius r / 6) -
        Real.log (2 * Real.pi * saddleVariance (saddleRadius r)) / 2) -
      ((r : ℝ)/4 - (r : ℝ)*Real.log (saddleScale r) + saddleScale r ^ 2/6 +
        saddleScale r/2 - 4/3 - Real.log (8 * Real.pi * (r : ℝ)) / 2 +
        ε * Real.log (saddleScale r / 6) + (6*ε-4)/saddleScale r)| ≤
      1000256 / saddleScale r ^ 2 := by
  have hr0 : 0 < r := by omega
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hb := saddleVariance_saddleRadius_pos r hr0
  let x := saddleScale r
  let ρ := saddleRadius r
  let D := (criticalPolynomial ρ - (r:ℝ)*Real.log ρ) -
    ((r:ℝ)/4 - (r:ℝ)*Real.log x + x^2/6 + x/2 - 4/3 - 4/x)
  let A := Real.log (1+ρ/6) - (Real.log (x/6) + 6/x)
  let V := Real.log (saddleVariance ρ) - Real.log (4*(r:ℝ))
  have hD : |D| ≤ 1000000/x^2 := saddleExponent_firstCorrection_explicit r hr
  have hA : |A| ≤ 152/x^2 := saddleAmplitude_log_firstCorrection_explicit r hr
  have hV : |V| ≤ 208/x^2 := saddleVariance_log_error_explicit r hr0
  have hεA : |ε*A| ≤ 152/x^2 := by
    rw [abs_mul, abs_of_nonneg hε0]
    calc
      ε*|A| ≤ 1*|A| := mul_le_mul_of_nonneg_right hε1 (abs_nonneg A)
      _ ≤ 152/x^2 := by simpa using hA
  have hV2 : |V/2| ≤ 104/x^2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
    calc
      |V|/2 ≤ (208/x^2)/2 := div_le_div_of_nonneg_right hV (by norm_num)
      _ = 104/x^2 := by ring
  have hlogs : Real.log (2 * Real.pi * saddleVariance ρ) -
      Real.log (8 * Real.pi * (r:ℝ)) = V := by
    rw [show 8 * Real.pi * (r:ℝ) = (2*Real.pi)*(4*(r:ℝ)) by ring]
    rw [Real.log_mul (by positivity : 2*Real.pi ≠ 0) hb.ne',
      Real.log_mul (by positivity : 2*Real.pi ≠ 0) (by positivity : 4*(r:ℝ) ≠ 0)]
    dsimp [V]
    ring
  have hid :
      (criticalPolynomial ρ - (r:ℝ)*Real.log ρ + ε*Real.log (1+ρ/6) -
        Real.log (2*Real.pi*saddleVariance ρ)/2) -
      ((r:ℝ)/4 - (r:ℝ)*Real.log x + x^2/6 + x/2 - 4/3 -
        Real.log (8*Real.pi*(r:ℝ))/2 + ε*Real.log (x/6) + (6*ε-4)/x) =
      D+ε*A-V/2 := by
    dsimp [D,A]
    linear_combination -hlogs/2
  change |_ - _| ≤ 1000256/x^2
  rw [hid]
  calc
    |D+ε*A-V/2| ≤ |D+ε*A|+|V/2| := abs_sub _ _
    _ ≤ (|D|+|ε*A|)+|V/2| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (1000000/x^2+152/x^2)+104/x^2 := add_le_add (add_le_add hD hεA) hV2
    _ = 1000256/x^2 := by ring

/-- Natural-parity version, with the exponent, amplitude, and normalization
kept in separate summands for subsequent multiplication by the other factors. -/
theorem saddleLog_firstCorrection (r : ℕ) (hr : 683 ≤ r)
    (ε : ℕ) (hε : ε ≤ 1) :
    |((ε:ℝ)*Real.log (1+saddleRadius r/6) +
        (criticalPolynomial (saddleRadius r)-(r:ℝ)*Real.log (saddleRadius r)) -
        (1/2:ℝ)*Real.log (2*Real.pi*saddleVariance (saddleRadius r))) -
      ((ε:ℝ)*(Real.log (saddleScale r/6)+6/saddleScale r) +
        ((r:ℝ)/4-(r:ℝ)*Real.log (saddleScale r)+saddleScale r^2/6+
          saddleScale r/2-4/3-4/saddleScale r) -
        (1/2:ℝ)*Real.log (8*Real.pi*(r:ℝ)))| ≤
      1000256/saddleScale r^2 := by
  convert saddleLog_firstCorrection_explicit r hr (ε:ℝ) (Nat.cast_nonneg ε)
    (by exact_mod_cast hε) using 2; ring

end SymmetricSubgroupAsymptotics
