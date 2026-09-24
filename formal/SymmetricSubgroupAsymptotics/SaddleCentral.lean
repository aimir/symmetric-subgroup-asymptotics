import SymmetricSubgroupAsymptotics.SaddleKernel

/-!
# A quantitative central-arc estimate

The real saddle kernel is compared with its Gaussian on the fixed arc
`[-π/4, π/4]`. Every estimate is uniform in the parity amplitude `0 ≤ d ≤ 1`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace SymmetricSubgroupAsymptotics

private theorem cos_remainder_bound (u : ℝ) :
    |Real.cos u - (1 - u ^ 2 / 2)| ≤ 3 * u ^ 4 := by
  by_cases hu : |u| ≤ 1
  · have h := Real.cos_bound hu
    have hp : |u| ^ 4 = u ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    rw [hp] at h
    nlinarith [sq_nonneg (u ^ 2)]
  · have hu1 : 1 ≤ |u| := (lt_of_not_ge hu).le
    have hu2 : 1 ≤ u ^ 2 := by nlinarith [sq_abs u]
    have hu4 : u ^ 2 ≤ u ^ 4 := by nlinarith [sq_nonneg (u ^ 2 - 1)]
    apply abs_le.mpr
    constructor <;> nlinarith [Real.neg_one_le_cos u, Real.cos_le_one u]

private theorem sin_remainder_bound (u : ℝ) :
    |Real.sin u - u| ≤ 2 * |u| ^ 3 := by
  by_cases hu : |u| ≤ 1
  · have h := Real.sin_bound hu
    have ht := abs_sub_le (Real.sin u) (u - u ^ 3 / 6) u
    have he : |u - u ^ 3 / 6 - u| = |u| ^ 3 / 6 := by
      rw [show u - u ^ 3 / 6 - u = -(u ^ 3 / 6) by ring,
        abs_neg, abs_div, abs_pow]
      norm_num
    rw [he] at ht
    have hp : |u| ^ 4 ≤ |u| ^ 3 := by
      nlinarith [mul_nonneg (pow_nonneg (abs_nonneg u) 3) (sub_nonneg.mpr hu)]
    nlinarith [pow_nonneg (abs_nonneg u) 3]
  · have hu1 : 1 ≤ |u| := (lt_of_not_ge hu).le
    have hp : |u| ≤ |u| ^ 3 := by nlinarith [sq_nonneg (|u| - 1)]
    have ht := (abs_sub (Real.sin u) u).trans
      (add_le_add (Real.abs_sin_le_one u) le_rfl)
    linarith

private theorem one_sub_cos_lower {u : ℝ} (hu : |u| ≤ Real.pi) :
    u ^ 2 / 8 ≤ 1 - Real.cos u := by
  have h := Real.cos_le_one_sub_mul_cos_sq hu
  have hpi : 0 < Real.pi ^ 2 := pow_pos Real.pi_pos 2
  have hp : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hconst : (1 / 8 : ℝ) ≤ 2 / Real.pi ^ 2 := by
    apply (le_div_iff₀ hpi).mpr
    linarith
  have hm := mul_le_mul_of_nonneg_right hconst (sq_nonneg u)
  nlinarith

theorem saddleDecay_central_lower (r : ℕ) (hr : 0 < r) {θ : ℝ}
    (hθ : |θ| ≤ Real.pi / 4) :
    (r : ℝ) * θ ^ 2 / 8 ≤ saddleDecay (saddleRadius r) θ := by
  let ρ := saddleRadius r
  have hρ : 0 ≤ ρ := (saddleRadius_pos r hr).le
  have h1 := one_sub_cos_lower (u := θ) (by linarith [Real.pi_pos])
  have h2 := one_sub_cos_lower (u := 2 * θ) (by simpa [abs_mul] using (show 2 * |θ| ≤ Real.pi by linarith [Real.pi_pos]))
  have h4 := one_sub_cos_lower (u := 4 * θ) (by simpa [abs_mul] using (show 4 * |θ| ≤ Real.pi by linarith))
  have hw1 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ ρ / 2 by positivity)
  have hw2 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ ρ ^ 2 / 6 by positivity)
  have hw4 := mul_le_mul_of_nonneg_left h4 (show 0 ≤ ρ ^ 4 / 384 by positivity)
  have hb := mul_le_mul_of_nonneg_right (saddleVariance_bounds r hr).1 (sq_nonneg θ)
  change (r : ℝ) * θ ^ 2 / 8 ≤ saddleDecay ρ θ
  change (r : ℝ) * θ ^ 2 ≤ saddleVariance ρ * θ ^ 2 at hb
  unfold saddleDecay saddleVariance at *
  nlinarith only [hw1, hw2, hw4, hb]

theorem saddleDecay_quadratic_error (r : ℕ) (hr : 0 < r) (θ : ℝ) :
    0 ≤ saddleVariance (saddleRadius r) * θ ^ 2 / 2 - saddleDecay (saddleRadius r) θ ∧
      saddleVariance (saddleRadius r) * θ ^ 2 / 2 - saddleDecay (saddleRadius r) θ ≤
        192 * (r : ℝ) * θ ^ 4 := by
  let ρ := saddleRadius r
  have hρ : 0 ≤ ρ := (saddleRadius_pos r hr).le
  have hm := saddleMean_saddleRadius r hr
  change saddleMean ρ = (r : ℝ) at hm
  have h1 := Real.one_sub_sq_div_two_le_cos (x := θ)
  have h2 := Real.one_sub_sq_div_two_le_cos (x := 2 * θ)
  have h4 := Real.one_sub_sq_div_two_le_cos (x := 4 * θ)
  have hl1 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ ρ / 2 by positivity)
  have hl2 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ ρ ^ 2 / 6 by positivity)
  have hl4 := mul_le_mul_of_nonneg_left h4 (show 0 ≤ ρ ^ 4 / 384 by positivity)
  have he1 := mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans (cos_remainder_bound θ))
    (show 0 ≤ ρ / 2 by positivity)
  have he2 := mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans (cos_remainder_bound (2 * θ)))
    (show 0 ≤ ρ ^ 2 / 6 by positivity)
  have he4 := mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans (cos_remainder_bound (4 * θ)))
    (show 0 ≤ ρ ^ 4 / 384 by positivity)
  have hweight : 3 * (ρ / 2 + 8 * ρ ^ 2 / 3 + 2 * ρ ^ 4 / 3) ≤ 192 * (r : ℝ) := by
    unfold saddleMean at hm
    nlinarith [sq_nonneg ρ]
  have hweight' := mul_le_mul_of_nonneg_right hweight (show 0 ≤ θ ^ 4 by positivity)
  change 0 ≤ saddleVariance ρ * θ ^ 2 / 2 - saddleDecay ρ θ ∧ _
  unfold saddleVariance saddleDecay
  constructor
  · nlinarith only [hl1, hl2, hl4]
  · nlinarith only [he1, he2, he4, hweight']

theorem saddlePhase_cubic_bound (r : ℕ) (hr : 0 < r) (θ : ℝ) :
    |saddlePhase (saddleRadius r) θ| ≤ 32 * (r : ℝ) * |θ| ^ 3 := by
  let ρ := saddleRadius r
  have hρ : 0 ≤ ρ := (saddleRadius_pos r hr).le
  have hm := saddleMean_saddleRadius r hr
  change saddleMean ρ = (r : ℝ) at hm
  have hweight : 2 * (ρ / 2 + 4 * ρ ^ 2 / 3 + ρ ^ 4 / 6) ≤ 32 * (r : ℝ) := by
    unfold saddleMean at hm
    nlinarith [sq_nonneg ρ]
  calc
    _ ≤ ρ / 2 * |Real.sin θ - θ| + ρ ^ 2 / 6 * |Real.sin (2 * θ) - 2 * θ| +
        ρ ^ 4 / 384 * |Real.sin (4 * θ) - 4 * θ| := by
      have ht := (abs_add_le (ρ / 2 * (Real.sin θ - θ) +
        ρ ^ 2 / 6 * (Real.sin (2 * θ) - 2 * θ))
        (ρ ^ 4 / 384 * (Real.sin (4 * θ) - 4 * θ))).trans
          (add_le_add (abs_add_le _ _) le_rfl)
      simpa only [saddlePhase, abs_mul, abs_of_nonneg (show 0 ≤ ρ / 2 by positivity),
        abs_of_nonneg (show 0 ≤ ρ ^ 2 / 6 by positivity),
        abs_of_nonneg (show 0 ≤ ρ ^ 4 / 384 by positivity)] using ht
    _ ≤ ρ / 2 * (2 * |θ| ^ 3) + ρ ^ 2 / 6 * (2 * |2 * θ| ^ 3) +
        ρ ^ 4 / 384 * (2 * |4 * θ| ^ 3) := by
      exact add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left (sin_remainder_bound θ) (by positivity))
          (mul_le_mul_of_nonneg_left (sin_remainder_bound (2 * θ)) (by positivity)))
        (mul_le_mul_of_nonneg_left (sin_remainder_bound (4 * θ)) (by positivity))
    _ = 2 * (ρ / 2 + 4 * ρ ^ 2 / 3 + ρ ^ 4 / 6) * |θ| ^ 3 := by
      simp only [abs_mul]
      norm_num
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hweight (by positivity)

private theorem abs_cos_sub_one_bound (u : ℝ) : |Real.cos u - 1| ≤ u ^ 2 / 2 := by
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one u))]
  linarith [Real.one_sub_sq_div_two_le_cos (x := u)]

private theorem amplitude_phase_bound {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (θ B : ℝ) :
    |(1 - d + d * Real.cos θ) * Real.cos B - d * Real.sin θ * Real.sin B - 1| ≤
      θ ^ 2 / 2 + |θ| * |B| + B ^ 2 / 2 := by
  have hv : |d * (Real.cos θ - 1) * Real.cos B| ≤ θ ^ 2 / 2 := by
    calc
      _ = d * |Real.cos θ - 1| * |Real.cos B| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hd0]
      _ ≤ 1 * (θ ^ 2 / 2) * 1 := by
        exact mul_le_mul
          (mul_le_mul hd1 (abs_cos_sub_one_bound θ) (abs_nonneg _) (by norm_num))
          (Real.abs_cos_le_one B) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hw : |d * Real.sin θ * Real.sin B| ≤ |θ| * |B| := by
    calc
      _ = d * |Real.sin θ| * |Real.sin B| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hd0]
      _ ≤ 1 * |θ| * |B| := by
        exact mul_le_mul
          (mul_le_mul hd1 Real.abs_sin_le_abs (abs_nonneg _) (by norm_num))
          Real.abs_sin_le_abs (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hu := abs_cos_sub_one_bound B
  have heq : (1 - d + d * Real.cos θ) * Real.cos B - d * Real.sin θ * Real.sin B - 1 =
      ((Real.cos B - 1) + d * (Real.cos θ - 1) * Real.cos B) -
        d * Real.sin θ * Real.sin B := by ring
  rw [heq]
  have htri : |(Real.cos B - 1) + d * (Real.cos θ - 1) * Real.cos B -
      d * Real.sin θ * Real.sin B| ≤ |Real.cos B - 1| +
        |d * (Real.cos θ - 1) * Real.cos B| + |d * Real.sin θ * Real.sin B| :=
    (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  linarith

private theorem kernel_amplitude_bound (r : ℕ) (hr : 0 < r)
    {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (θ : ℝ) :
    |(1 - d + d * Real.cos θ) * Real.cos (saddlePhase (saddleRadius r) θ) -
      d * Real.sin θ * Real.sin (saddlePhase (saddleRadius r) θ) - 1| ≤
      θ ^ 2 / 2 + 32 * (r : ℝ) * θ ^ 4 + 512 * (r : ℝ) ^ 2 * θ ^ 6 := by
  let B := saddlePhase (saddleRadius r) θ
  have hb : |B| ≤ 32 * (r : ℝ) * |θ| ^ 3 := saddlePhase_cubic_bound r hr θ
  have hmul := mul_le_mul_of_nonneg_left hb (abs_nonneg θ)
  have hsq := pow_le_pow_left₀ (abs_nonneg B) hb 2
  have hp4 : |θ| ^ 4 = θ ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hp6 : |θ| ^ 6 = θ ^ 6 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  rw [sq_abs] at hsq
  have hmul' : |θ| * |B| ≤ 32 * (r : ℝ) * θ ^ 4 := by
    calc
      _ ≤ |θ| * (32 * (r : ℝ) * |θ| ^ 3) := hmul
      _ = _ := by rw [← hp4]; ring
  have hsq' : B ^ 2 / 2 ≤ 512 * (r : ℝ) ^ 2 * θ ^ 6 := by
    have heq : (32 * (r : ℝ) * |θ| ^ 3) ^ 2 = 1024 * (r : ℝ) ^ 2 * θ ^ 6 := by
      rw [← hp6]
      ring
    rw [heq] at hsq
    linarith
  have ha := amplitude_phase_bound hd0 hd1 θ B
  exact ha.trans (by linarith)

private theorem exp_neg_difference {A Q : ℝ} (hAQ : A ≤ Q) :
    0 ≤ Real.exp (-A) - Real.exp (-Q) ∧
      Real.exp (-A) - Real.exp (-Q) ≤ Real.exp (-A) * (Q - A) := by
  have hnon : Real.exp (-Q) ≤ Real.exp (-A) := Real.exp_le_exp.mpr (by linarith)
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (A - Q)) (Real.exp_pos (-A)).le
  have he : Real.exp (-A) * Real.exp (A - Q) = Real.exp (-Q) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  constructor <;> nlinarith

/-- An explicit Gaussian-times-polynomial majorant on the fixed central arc. -/
theorem saddleCentral_pointwise (r : ℕ) (hr : 0 < r) {d θ : ℝ}
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hθ : |θ| ≤ Real.pi / 4) :
    |saddleRealKernel (saddleRadius r) d θ - saddleGaussian (saddleRadius r) θ| ≤
      Real.exp (-(r : ℝ) * θ ^ 2 / 8) *
        (θ ^ 2 / 2 + 224 * (r : ℝ) * θ ^ 4 + 512 * (r : ℝ) ^ 2 * θ ^ 6) := by
  let A := saddleDecay (saddleRadius r) θ
  let Q := saddleVariance (saddleRadius r) * θ ^ 2 / 2
  let F := (1 - d + d * Real.cos θ) * Real.cos (saddlePhase (saddleRadius r) θ) -
    d * Real.sin θ * Real.sin (saddlePhase (saddleRadius r) θ)
  have hquad := saddleDecay_quadratic_error r hr θ
  have hAQ : A ≤ Q := by dsimp [A, Q]; linarith [hquad.1]
  have hdifference := exp_neg_difference hAQ
  have hamp : |F - 1| ≤ θ ^ 2 / 2 + 32 * (r : ℝ) * θ ^ 4 +
      512 * (r : ℝ) ^ 2 * θ ^ 6 := kernel_amplitude_bound r hr hd0 hd1 θ
  have heq : saddleRealKernel (saddleRadius r) d θ - saddleGaussian (saddleRadius r) θ =
      Real.exp (-A) * (F - 1) + (Real.exp (-A) - Real.exp (-Q)) := by
    dsimp [saddleRealKernel, saddleGaussian, A, Q, F]
    rw [show -(saddleVariance (saddleRadius r)) * θ ^ 2 / 2 =
      -(saddleVariance (saddleRadius r) * θ ^ 2 / 2) by ring]
    ring
  have hpre : |saddleRealKernel (saddleRadius r) d θ - saddleGaussian (saddleRadius r) θ| ≤
      Real.exp (-A) *
        (θ ^ 2 / 2 + 224 * (r : ℝ) * θ ^ 4 + 512 * (r : ℝ) ^ 2 * θ ^ 6) := by
    rw [heq]
    have htri := abs_add_le (Real.exp (-A) * (F - 1)) (Real.exp (-A) - Real.exp (-Q))
    rw [abs_mul, abs_of_nonneg (Real.exp_pos (-A)).le,
      abs_of_nonneg hdifference.1] at htri
    have hamul := mul_le_mul_of_nonneg_left hamp (Real.exp_pos (-A)).le
    have hqmul := mul_le_mul_of_nonneg_left hquad.2 (Real.exp_pos (-A)).le
    change Real.exp (-A) * (Q - A) ≤ _ at hqmul
    nlinarith only [htri, hamul, hqmul, hdifference.2]
  have hdec := saddleDecay_central_lower r hr hθ
  have hexp : Real.exp (-A) ≤ Real.exp (-(r : ℝ) * θ ^ 2 / 8) := by
    apply Real.exp_le_exp.mpr
    dsimp [A]
    linarith
  exact hpre.trans (mul_le_mul_of_nonneg_right hexp (by positivity))

private theorem absorb_polynomial {R : ℝ} (hR : 0 < R) (θ : ℝ) :
    Real.exp (-R * θ ^ 2 / 8) *
      (θ ^ 2 / 2 + 224 * R * θ ^ 4 + 512 * R ^ 2 * θ ^ 6) ≤
        (16777216 / R) * Real.exp (-R * θ ^ 2 / 16) := by
  let u := R * θ ^ 2 / 16
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have h1 := Real.pow_div_factorial_le_exp u hu 1
  have h2 := Real.pow_div_factorial_le_exp u hu 2
  have h3 := Real.pow_div_factorial_le_exp u hu 3
  norm_num at h1 h2 h3
  have hpoly : 8 * u + 57344 * u ^ 2 + 2097152 * u ^ 3 ≤
      16777216 * Real.exp u := by
    nlinarith [Real.exp_pos u]
  have hmul := mul_le_mul_of_nonneg_right hpoly
    (show 0 ≤ (1 / R) * Real.exp (-u) * Real.exp (-u) by positivity)
  have hcancel : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have he : Real.exp (-R * θ ^ 2 / 8) = Real.exp (-u) * Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [u]
    ring
  have hl : Real.exp (-R * θ ^ 2 / 8) *
      (θ ^ 2 / 2 + 224 * R * θ ^ 4 + 512 * R ^ 2 * θ ^ 6) =
        (8 * u + 57344 * u ^ 2 + 2097152 * u ^ 3) *
          ((1 / R) * Real.exp (-u) * Real.exp (-u)) := by
    rw [he]
    dsimp [u]
    field_simp
    ring
  have hrhs : (16777216 * Real.exp u) *
      ((1 / R) * Real.exp (-u) * Real.exp (-u)) =
        (16777216 / R) * Real.exp (-R * θ ^ 2 / 16) := by
    calc
      _ = (16777216 / R) * (Real.exp u * Real.exp (-u)) * Real.exp (-u) := by ring
      _ = _ := by
        rw [hcancel, mul_one]
        congr 1
        dsimp [u]
        congr 1
        ring
  rw [hl, ← hrhs]
  exact hmul

/-- A single Gaussian envelope absorbs all central Taylor-error terms. -/
theorem saddleCentral_gaussian_majorant (r : ℕ) (hr : 0 < r) {d θ : ℝ}
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hθ : |θ| ≤ Real.pi / 4) :
    |saddleRealKernel (saddleRadius r) d θ - saddleGaussian (saddleRadius r) θ| ≤
      (16777216 / (r : ℝ)) * Real.exp (-(r : ℝ) * θ ^ 2 / 16) :=
  (saddleCentral_pointwise r hr hd0 hd1 hθ).trans
    (absorb_polynomial (by exact_mod_cast hr) θ)

private theorem gaussian_majorant_integral {R : ℝ} (hR : 0 < R) :
    (∫ θ : ℝ, (16777216 / R) * Real.exp (-R * θ ^ 2 / 16)) ≤
      134217728 / (R * Real.sqrt R) := by
  have heq : (fun θ : ℝ ↦ Real.exp (-R * θ ^ 2 / 16)) =
      (fun θ : ℝ ↦ Real.exp (-(R / 16) * θ ^ 2)) := by
    funext θ
    congr 1
    ring
  rw [integral_const_mul, heq, integral_gaussian]
  have hroot : Real.sqrt (Real.pi / (R / 16)) ≤ 8 / Real.sqrt R := by
    rw [show Real.pi / (R / 16) = (16 * Real.pi) / R by field_simp,
      Real.sqrt_div (by positivity)]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg R)
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · nlinarith [Real.pi_lt_four]
  calc
    _ ≤ (16777216 / R) * (8 / Real.sqrt R) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = _ := by ring

/-- The whole central-arc error is `O(r^(-3/2))`, with a fixed positive
constant and no asymptotic or parity hypotheses beyond `r>0` and `0≤d≤1`. -/
theorem saddleCentral_integral_error (r : ℕ) (hr : 0 < r) {d : ℝ}
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    |(∫ θ in (-Real.pi / 4)..(Real.pi / 4), saddleRealKernel (saddleRadius r) d θ) -
      (∫ θ in (-Real.pi / 4)..(Real.pi / 4), saddleGaussian (saddleRadius r) θ)| ≤
        134217728 / ((r : ℝ) * Real.sqrt (r : ℝ)) := by
  let a := -Real.pi / 4
  let b := Real.pi / 4
  let M := fun θ : ℝ ↦ (16777216 / (r : ℝ)) * Real.exp (-(r : ℝ) * θ ^ 2 / 16)
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hab : a ≤ b := by dsimp [a, b]; linarith [Real.pi_pos]
  have hH := (continuous_saddleRealKernel (saddleRadius r) d).intervalIntegrable (μ := volume) a b
  have hG := (continuous_saddleGaussian (saddleRadius r)).intervalIntegrable (μ := volume) a b
  have hdiff := ((continuous_saddleRealKernel (saddleRadius r) d).sub
    (continuous_saddleGaussian (saddleRadius r))).abs.intervalIntegrable (μ := volume) a b
  have hMc : Continuous M := by dsimp [M]; fun_prop
  have hMi : Integrable M := by
    have h := (integrable_exp_neg_mul_sq (show 0 < (r : ℝ) / 16 by positivity)).const_mul
      (16777216 / (r : ℝ))
    convert h using 1
    funext θ
    dsimp [M]
    congr 2
    ring
  rw [← intervalIntegral.integral_sub hH hG]
  calc
    _ ≤ ∫ θ in a..b, |saddleRealKernel (saddleRadius r) d θ - saddleGaussian (saddleRadius r) θ| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ θ in a..b, M θ := by
      apply intervalIntegral.integral_mono_on hab hdiff (hMc.intervalIntegrable a b)
      intro θ hθ
      apply saddleCentral_gaussian_majorant r hr hd0 hd1
      apply abs_le.mpr
      dsimp [a, b] at hθ
      constructor <;> linarith [hθ.1, hθ.2]
    _ ≤ ∫ θ : ℝ, M θ := by
      rw [intervalIntegral.integral_of_le hab]
      exact setIntegral_le_integral hMi (Filter.Eventually.of_forall fun θ ↦ by dsimp [M]; positivity)
    _ ≤ _ := gaussian_majorant_integral hr'

end SymmetricSubgroupAsymptotics
