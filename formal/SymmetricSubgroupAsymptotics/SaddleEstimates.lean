import SymmetricSubgroupAsymptotics.Saddle

/-!
# Quantitative estimates for the positive saddle

These are estimates for the actual, previously constructed positive root.
The constants are deliberately uniform; no asymptotic assertion is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The leading fourth-root scale of the saddle. -/
def saddleScale (r : ℕ) : ℝ := (96 * (r : ℝ)) ^ (1 / 4 : ℝ)

theorem saddleScale_nonneg (r : ℕ) : 0 ≤ saddleScale r := by
  unfold saddleScale
  positivity

theorem saddleScale_pos (r : ℕ) (hr : 0 < r) : 0 < saddleScale r := by
  unfold saddleScale
  positivity

theorem saddleScale_pow_four (r : ℕ) : saddleScale r ^ 4 = 96 * (r : ℝ) := by
  unfold saddleScale
  rw [← Real.rpow_mul_natCast (by positivity) (1 / 4 : ℝ) 4]
  norm_num

theorem saddleRadius_quartic (r : ℕ) (hr : 0 < r) :
    saddleRadius r ^ 4 + 32 * saddleRadius r ^ 2 + 48 * saddleRadius r =
      saddleScale r ^ 4 := by
  have hm := saddleMean_saddleRadius r hr
  unfold saddleMean at hm
  rw [saddleScale_pow_four]
  linarith

theorem one_le_saddleScale (r : ℕ) (hr : 0 < r) : 1 ≤ saddleScale r := by
  have hp := saddleScale_pow_four r
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 1)
    (saddleScale_nonneg r) (show 4 ≠ 0 by decide)).mp
  norm_num
  linarith

theorem saddleRadius_le_scale (r : ℕ) (hr : 0 < r) :
    saddleRadius r ≤ saddleScale r := by
  apply (saddleMean_strictMonoOn.le_iff_le
    (saddleRadius_pos r hr).le (saddleScale_nonneg r)).mp
  rw [saddleMean_saddleRadius r hr]
  have hx := saddleScale_pow_four r
  have hn := saddleScale_nonneg r
  unfold saddleMean
  nlinarith [sq_nonneg (saddleScale r)]

/-- An absolute error bound of order `r^(-1/4)`, valid at every positive rank. -/
theorem saddleRadius_scale_error (r : ℕ) (hr : 0 < r) :
    0 ≤ saddleScale r - saddleRadius r ∧
      saddleScale r - saddleRadius r ≤ 80 / saddleScale r := by
  let x := saddleScale r
  let ρ := saddleRadius r
  have hx : 0 < x := saddleScale_pos r hr
  have hx1 : 1 ≤ x := one_le_saddleScale r hr
  have hρ : 0 < ρ := saddleRadius_pos r hr
  have hle : ρ ≤ x := saddleRadius_le_scale r hr
  have hq : ρ ^ 4 + 32 * ρ ^ 2 + 48 * ρ = x ^ 4 := saddleRadius_quartic r hr
  have hd : 0 ≤ x - ρ := sub_nonneg.mpr hle
  refine ⟨hd, ?_⟩
  have hs : ρ ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hρ.le hle 2
  have hg : 0 ≤ (x - ρ) * (x ^ 2 * ρ + x * ρ ^ 2 + ρ ^ 3) :=
    mul_nonneg hd (by positivity)
  have hx2 : x ≤ x ^ 2 := by nlinarith
  have hmain : ((x - ρ) * x) * x ^ 2 ≤ 80 * x ^ 2 := by
    nlinarith
  have hcancel : (x - ρ) * x ≤ 80 :=
    (mul_le_mul_iff_of_pos_right (pow_pos hx 2)).mp hmain
  exact (le_div_iff₀ hx).mpr hcancel

/-- The leading-scale relative error is already of order `r^(-1/2)`. -/
theorem saddleRadius_relative_error (r : ℕ) (hr : 0 < r) :
    |saddleRadius r / saddleScale r - 1| ≤ 80 / saddleScale r ^ 2 := by
  have hx := saddleScale_pos r hr
  have hle := saddleRadius_le_scale r hr
  have he := (saddleRadius_scale_error r hr).2
  have hratio : saddleRadius r / saddleScale r ≤ 1 := (div_le_one hx).mpr hle
  rw [abs_of_nonpos (sub_nonpos.mpr hratio)]
  have hd := div_le_div_of_nonneg_right he hx.le
  calc
    -(saddleRadius r / saddleScale r - 1) =
        (saddleScale r - saddleRadius r) / saddleScale r := by
      rw [sub_div, div_self hx.ne']
      ring
    _ ≤ (80 / saddleScale r) / saddleScale r := hd
    _ = 80 / saddleScale r ^ 2 := by ring

/-- Exact variance deficit; in particular the dominant term is `4r`. -/
theorem saddleVariance_deficit (r : ℕ) (hr : 0 < r) :
    4 * (r : ℝ) - saddleVariance (saddleRadius r) =
      3 * saddleRadius r / 2 + 2 * saddleRadius r ^ 2 / 3 := by
  have hm := saddleMean_saddleRadius r hr
  unfold saddleMean at hm
  unfold saddleVariance
  linarith

/-- A uniform relative error estimate for the variance. -/
theorem saddleVariance_relative_error (r : ℕ) (hr : 0 < r) :
    |saddleVariance (saddleRadius r) / (4 * (r : ℝ)) - 1| ≤
      52 / saddleScale r ^ 2 := by
  let x := saddleScale r
  let ρ := saddleRadius r
  have hx : 0 < x := saddleScale_pos r hr
  have hx1 : 1 ≤ x := one_le_saddleScale r hr
  have hρ : 0 < ρ := saddleRadius_pos r hr
  have hle : ρ ≤ x := saddleRadius_le_scale r hr
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hdef := saddleVariance_deficit r hr
  have hvariance := (saddleVariance_bounds r hr).2
  have hratio : saddleVariance ρ / (4 * (r : ℝ)) ≤ 1 :=
    (div_le_one (by positivity)).mpr hvariance
  have hs : ρ ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hρ.le hle 2
  have hx2 : x ≤ x ^ 2 := by nlinarith
  have hbound : 4 * (r : ℝ) - saddleVariance ρ ≤ 13 * x ^ 2 / 6 := by
    dsimp [ρ] at *
    linarith
  have hp : x ^ 4 = 96 * (r : ℝ) := saddleScale_pow_four r
  rw [abs_of_nonpos (sub_nonpos.mpr hratio)]
  have hd := div_le_div_of_nonneg_right hbound (show 0 ≤ 4 * (r : ℝ) by positivity)
  have hid : (13 * x ^ 2 / 6) / (4 * (r : ℝ)) = 52 / x ^ 2 := by
    field_simp
    nlinarith
  rw [hid] at hd
  have hid' : -(saddleVariance ρ / (4 * (r : ℝ)) - 1) =
      (4 * (r : ℝ) - saddleVariance ρ) / (4 * (r : ℝ)) := by
    rw [sub_div, div_self (by positivity : 4 * (r : ℝ) ≠ 0)]
    ring
  rw [hid']
  exact hd

private def quartic (x : ℝ) : ℝ := x ^ 4 + 32 * x ^ 2 + 48 * x

private theorem quartic_growth {x u v : ℝ} (hx : 0 ≤ x)
    (hu : x / 2 ≤ u) (huv : u ≤ v) :
    (v - u) * x ^ 3 ≤ 2 * (quartic v - quartic u) := by
  have hu0 : 0 ≤ u := le_trans (by positivity) hu
  have hv0 : 0 ≤ v := le_trans hu0 huv
  have hu3 : (x / 2) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ (by positivity) hu 3
  have hv3 : u ^ 3 ≤ v ^ 3 := pow_le_pow_left₀ hu0 huv 3
  have huv2 : u ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ hu0 huv 2
  have hmix1 : u ^ 3 ≤ u ^ 2 * v := by
    nlinarith [mul_le_mul_of_nonneg_left huv (sq_nonneg u)]
  have hmix2 : u ^ 3 ≤ u * v ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left huv2 hu0]
  have hfactor : x ^ 3 ≤
      2 * (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3 + 32 * (u + v) + 48) := by
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hfactor (sub_nonneg.mpr huv)
  unfold quartic
  nlinarith only [hh]

private theorem quartic_inverse_bound {x u v : ℝ} (hx : 0 ≤ x)
    (hu : x / 2 ≤ u) (hv : x / 2 ≤ v) :
    |u - v| * x ^ 3 ≤ 2 * |quartic u - quartic v| := by
  rcases le_total u v with huv | hvu
  · have hg := quartic_growth hx hu huv
    have hq : quartic u ≤ quartic v := by
      have hn : 0 ≤ (v - u) * x ^ 3 := by positivity
      linarith
    rw [abs_of_nonpos (sub_nonpos.mpr huv), abs_of_nonpos (sub_nonpos.mpr hq)]
    nlinarith only [hg]
  · have hg := quartic_growth hx hv hvu
    have hq : quartic v ≤ quartic u := by
      have hn : 0 ≤ (u - v) * x ^ 3 := by positivity
      linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hvu), abs_of_nonneg (sub_nonneg.mpr hq)]
    exact hg

private theorem correction_bounds {x : ℝ} (hx : 16 ≤ x) :
    let d := 8 / x + 12 / x ^ 2
    0 ≤ d ∧ d ≤ 1 ∧ x * d ≤ 9 ∧ x / 2 ≤ x - d := by
  have hx0 : 0 < x := by linarith
  dsimp
  have hd0 : 0 ≤ 8 / x + 12 / x ^ 2 := by positivity
  have hdx : x * (8 / x + 12 / x ^ 2) = 8 + 12 / x := by
    field_simp
  have hx12 : 12 / x ≤ 1 := (div_le_one hx0).mpr (by linarith)
  have hdx9 : x * (8 / x + 12 / x ^ 2) ≤ 9 := by linarith
  have hd1 : 8 / x + 12 / x ^ 2 ≤ 1 := by nlinarith
  exact ⟨hd0, hd1, hdx9, by linarith⟩

private theorem quartic_correction_residual {x : ℝ} (hx : 16 ≤ x) :
    |quartic (x - 8 / x - 12 / x ^ 2) - x ^ 4| ≤ 1024 := by
  have hx0 : 0 < x := by linarith
  let d := 8 / x + 12 / x ^ 2
  obtain ⟨hd0, hd1, hdx, _⟩ := correction_bounds hx
  change 0 ≤ d at hd0
  change d ≤ 1 at hd1
  change x * d ≤ 9 at hdx
  have hd2 : d ^ 2 ≤ 1 := by nlinarith
  have hd4 : d ^ 4 ≤ 1 := by nlinarith [sq_nonneg (d ^ 2 - 1)]
  have hxd0 : 0 ≤ x * d := by positivity
  have hxd2 : (x * d) ^ 2 ≤ 81 := by nlinarith
  have hxd3 : (x * d) * d ^ 2 ≤ 9 := by
    nlinarith [mul_le_mul_of_nonneg_left hd2 hxd0]
  have hcancel : 4 * x ^ 3 * d = 32 * x ^ 2 + 48 * x := by
    dsimp [d]
    field_simp
    ring
  have hid : quartic (x - 8 / x - 12 / x ^ 2) - x ^ 4 =
      6 * (x * d) ^ 2 - 64 * (x * d) - 4 * (x * d) * d ^ 2 +
        d ^ 4 + 32 * d ^ 2 - 48 * d := by
    have hy : x - 8 / x - 12 / x ^ 2 = x - d := by dsimp [d]; ring
    rw [hy]
    unfold quartic
    nlinarith only [hcancel]
  rw [hid]
  apply abs_le.mpr
  have hxd3nonneg : 0 ≤ (x * d) * d ^ 2 := by positivity
  constructor <;> nlinarith [sq_nonneg d, sq_nonneg (d ^ 2), sq_nonneg (x * d)]

theorem sixteen_le_saddleScale (r : ℕ) (hr : 683 ≤ r) : 16 ≤ saddleScale r := by
  apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 16)
    (saddleScale_nonneg r) (show 4 ≠ 0 by decide)).mp
  rw [saddleScale_pow_four]
  have hr' : (683 : ℝ) ≤ r := by exact_mod_cast hr
  norm_num
  linarith

theorem half_scale_le_saddleRadius (r : ℕ) (hr : 683 ≤ r) :
    saddleScale r / 2 ≤ saddleRadius r := by
  have hr0 : 0 < r := by omega
  let x := saddleScale r
  have hx : 16 ≤ x := sixteen_le_saddleScale r hr
  have hx0 : 0 ≤ x := saddleScale_nonneg r
  have hp : x ^ 4 = 96 * (r : ℝ) := saddleScale_pow_four r
  have hx2 : 4 * x ≤ x ^ 2 := by nlinarith
  have hx4 : 16 * x ^ 2 ≤ x ^ 4 := by
    have hh : 16 ≤ x ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hh)]
  apply (saddleMean_strictMonoOn.le_iff_le
    (show 0 ≤ x / 2 by positivity) (saddleRadius_pos r hr0).le).mp
  rw [saddleMean_saddleRadius r hr0]
  unfold saddleMean
  nlinarith

/-- A fully quantitative two-correction expansion, with a common explicit
threshold and constant. In particular its remainder is `O(r^(-3/4))`. -/
theorem saddleRadius_expansion (r : ℕ) (hr : 683 ≤ r) :
    |saddleRadius r -
      (saddleScale r - 8 / saddleScale r - 12 / saddleScale r ^ 2)| ≤
        2048 / saddleScale r ^ 3 := by
  have hr0 : 0 < r := by omega
  let x := saddleScale r
  let ρ := saddleRadius r
  let y := x - 8 / x - 12 / x ^ 2
  have hx : 16 ≤ x := sixteen_le_saddleScale r hr
  have hx0 : 0 < x := saddleScale_pos r hr0
  have hρ : x / 2 ≤ ρ := half_scale_le_saddleRadius r hr
  have hy : x / 2 ≤ y := by
    have hb := (correction_bounds hx).2.2.2
    dsimp [y]
    linarith
  have hq : quartic ρ = x ^ 4 := saddleRadius_quartic r hr0
  have hinv := quartic_inverse_bound hx0.le hρ hy
  have hres : |quartic y - x ^ 4| ≤ 1024 := quartic_correction_residual hx
  rw [hq, abs_sub_comm (x ^ 4)] at hinv
  apply (le_div_iff₀ (pow_pos hx0 3)).mpr
  linarith

theorem saddleScale_tendsto_atTop :
    Filter.Tendsto saddleScale Filter.atTop Filter.atTop := by
  unfold saddleScale
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 96))

/-- The positive saddle is asymptotic to its explicit fourth-root scale. -/
theorem saddleRadius_div_scale_tendsto_one :
    Filter.Tendsto (fun r : ℕ ↦ saddleRadius r / saddleScale r)
      Filter.atTop (nhds 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)
  · filter_upwards [Filter.eventually_ge_atTop 1] with r hr
    exact saddleRadius_relative_error r (by omega)
  · exact tendsto_const_nhds.div_atTop
      ((Filter.tendsto_pow_atTop (by decide : 2 ≠ 0)).comp saddleScale_tendsto_atTop)

/-- The variance is asymptotic to `4r`, with the rate proved above. -/
theorem saddleVariance_div_four_rank_tendsto_one :
    Filter.Tendsto (fun r : ℕ ↦ saddleVariance (saddleRadius r) / (4 * (r : ℝ)))
      Filter.atTop (nhds 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)
  · filter_upwards [Filter.eventually_ge_atTop 1] with r hr
    exact saddleVariance_relative_error r (by omega)
  · exact tendsto_const_nhds.div_atTop
      ((Filter.tendsto_pow_atTop (by decide : 2 ≠ 0)).comp saddleScale_tendsto_atTop)

end SymmetricSubgroupAsymptotics
