import SymmetricSubgroupAsymptotics.SaddleKernel

/-!
# Quantified outer-arc and Gaussian-tail bounds

The central arc is fixed at `[-π/4, π/4]`. The linear term in the saddle
loss controls the remaining circle, uniformly in the parity amplitude.
The comparison Gaussian is integrated on the whole real line. Both tails
have proved eventual inverse-power bounds, rather than assumed decay.
-/

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set

namespace SymmetricSubgroupAsymptotics

/-- Outside the fixed central arc, the first harmonic already supplies a
uniform positive loss. -/
theorem one_sub_cos_ge_eighth {θ : ℝ}
    (hθlow : Real.pi / 4 ≤ |θ|) (hθhigh : |θ| ≤ Real.pi) :
    (1 / 8 : ℝ) ≤ 1 - Real.cos θ := by
  have hcos : Real.cos θ ≤ Real.cos (Real.pi / 4) := by
    simpa only [Real.cos_abs] using Real.cos_le_cos_of_nonneg_of_le_pi
      (by positivity : 0 ≤ Real.pi / 4) hθhigh hθlow
  rw [Real.cos_pi_div_four] at hcos
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hroot : Real.sqrt 2 ≤ 3 / 2 := by
    nlinarith [sq_nonneg (Real.sqrt 2 - 2)]
  linarith

theorem saddleDecay_outer_lower {ρ θ : ℝ} (hρ : 0 ≤ ρ)
    (hθlow : Real.pi / 4 ≤ |θ|) (hθhigh : |θ| ≤ Real.pi) :
    ρ / 16 ≤ saddleDecay ρ θ := by
  have h1 := mul_le_mul_of_nonneg_left (one_sub_cos_ge_eighth hθlow hθhigh)
    (show 0 ≤ ρ / 2 by positivity)
  have h2 : 0 ≤ (ρ ^ 2 / 6) * (1 - Real.cos (2 * θ)) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one _))
  have h4 : 0 ≤ (ρ ^ 4 / 384) * (1 - Real.cos (4 * θ)) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one _))
  unfold saddleDecay
  nlinarith

/-- The real amplitude is a convex combination of two cosines. -/
theorem saddleRealKernel_abs_le_exp_neg_decay (ρ d θ : ℝ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    |saddleRealKernel ρ d θ| ≤ Real.exp (-saddleDecay ρ θ) := by
  have hidentity : (1 - d + d * Real.cos θ) * Real.cos (saddlePhase ρ θ) -
      d * Real.sin θ * Real.sin (saddlePhase ρ θ) =
      (1 - d) * Real.cos (saddlePhase ρ θ) + d * Real.cos (θ + saddlePhase ρ θ) := by
    rw [Real.cos_add]
    ring
  have hamp : |(1 - d) * Real.cos (saddlePhase ρ θ) +
      d * Real.cos (θ + saddlePhase ρ θ)| ≤ 1 := by
    calc
      _ ≤ |(1 - d) * Real.cos (saddlePhase ρ θ)| +
          |d * Real.cos (θ + saddlePhase ρ θ)| := abs_add_le _ _
      _ = (1 - d) * |Real.cos (saddlePhase ρ θ)| +
          d * |Real.cos (θ + saddlePhase ρ θ)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hd1), abs_of_nonneg hd0]
      _ ≤ (1 - d) * 1 + d * 1 := add_le_add
        (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (sub_nonneg.mpr hd1))
        (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hd0)
      _ = 1 := by ring
  rw [saddleRealKernel, hidentity, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (Real.exp_pos _).le hamp

theorem saddleRealKernel_outer_bound {ρ d θ : ℝ} (hρ : 0 ≤ ρ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hθlow : Real.pi / 4 ≤ |θ|) (hθhigh : |θ| ≤ Real.pi) :
    |saddleRealKernel ρ d θ| ≤ Real.exp (-ρ / 16) := by
  apply (saddleRealKernel_abs_le_exp_neg_decay ρ d θ hd0 hd1).trans
  apply Real.exp_le_exp.mpr
  have := saddleDecay_outer_lower hρ hθlow hθhigh
  linarith

/-- The two outer arcs of the coefficient circle have a uniform integral
bound, including both parity amplitudes. -/
theorem saddle_outer_integral_bound {ρ d : ℝ} (hρ : 0 ≤ ρ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    |(∫ θ in (-Real.pi)..(-Real.pi / 4), saddleRealKernel ρ d θ) +
      (∫ θ in (Real.pi / 4)..Real.pi, saddleRealKernel ρ d θ)| ≤
        2 * Real.pi * Real.exp (-ρ / 16) := by
  have hπ := Real.pi_pos
  have hleft : |∫ θ in (-Real.pi)..(-Real.pi / 4), saddleRealKernel ρ d θ| ≤
      Real.exp (-ρ / 16) * |-Real.pi / 4 - (-Real.pi)| := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro θ hθ
    rw [Set.uIoc_of_le (by linarith : -Real.pi ≤ -Real.pi / 4)] at hθ
    have hθ0 : θ ≤ 0 := by have := hθ.2; linarith
    simpa only [Real.norm_eq_abs] using saddleRealKernel_outer_bound hρ hd0 hd1
      (by rw [abs_of_nonpos hθ0]; have := hθ.2; linarith)
      (by rw [abs_of_nonpos hθ0]; have := hθ.1; linarith)
  have hright : |∫ θ in (Real.pi / 4)..Real.pi, saddleRealKernel ρ d θ| ≤
      Real.exp (-ρ / 16) * |Real.pi - Real.pi / 4| := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro θ hθ
    rw [Set.uIoc_of_le (by linarith : Real.pi / 4 ≤ Real.pi)] at hθ
    have hθ0 : 0 ≤ θ := by have := hθ.1; linarith
    simpa only [Real.norm_eq_abs] using saddleRealKernel_outer_bound hρ hd0 hd1
      (by rw [abs_of_nonneg hθ0]; exact hθ.1.le)
      (by rw [abs_of_nonneg hθ0]; exact hθ.2)
  have hlenL : |-Real.pi / 4 - (-Real.pi)| ≤ Real.pi := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hlenR : |Real.pi - Real.pi / 4| ≤ Real.pi := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hL := hleft.trans (mul_le_mul_of_nonneg_left hlenL (Real.exp_pos _).le)
  have hR := hright.trans (mul_le_mul_of_nonneg_left hlenR (Real.exp_pos _).le)
  have hsum := abs_add_le
    (∫ θ in (-Real.pi)..(-Real.pi / 4), saddleRealKernel ρ d θ)
    (∫ θ in (Real.pi / 4)..Real.pi, saddleRealKernel ρ d θ)
  nlinarith

/-- Ordinary exponential decay absorbs any fixed real power after a proved
threshold. -/
theorem eventually_exp_neg_mul_le_inv_rpow {c : ℝ} (hc : 0 < c) (p : ℝ) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-c * (n : ℝ)) ≤ 1 / (n : ℝ) ^ p := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p c hc).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop 1] with n hn hn1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hnpos p)).mpr
  simpa only [Function.comp_apply, mul_comm] using hn.le

/-- Exponential decay in the fourth-root saddle scale still absorbs every
fixed inverse integral power of the rank. -/
theorem eventually_saddle_exp_le_inv_pow (p : ℕ) :
    ∀ᶠ r : ℕ in atTop, Real.exp (-saddleRadius r / 16) ≤ 1 / (r : ℝ) ^ p := by
  have ht : Tendsto (fun r : ℕ => saddleScale r ^ (4 * p) *
      Real.exp (-saddleScale r / 32)) atTop (nhds 0) := by
    convert (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((4 * p : ℕ) : ℝ)
      (1 / 32) (by norm_num)).comp saddleScale_tendsto_atTop using 1
    ext r
    simp only [Function.comp_apply, Real.rpow_natCast]
    congr 1
    congr 1
    ring
  filter_upwards [ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop 683] with r htR hr
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hscale := half_scale_le_saddleRadius r hr
  have hexp : Real.exp (-saddleRadius r / 16) ≤ Real.exp (-saddleScale r / 32) :=
    Real.exp_le_exp.mpr (by linarith)
  have hpoly : (r : ℝ) ^ p ≤ saddleScale r ^ (4 * p) := by
    have hbase : (r : ℝ) ≤ saddleScale r ^ 4 := by
      rw [saddleScale_pow_four]
      linarith
    simpa only [← pow_mul] using pow_le_pow_left₀ hrpos.le hbase p
  have hmul := mul_le_mul hpoly hexp (Real.exp_pos _).le
    (pow_nonneg (saddleScale_nonneg r) (4 * p))
  apply (le_div_iff₀ (pow_pos hrpos p)).mpr
  nlinarith

/-- The outer saddle arcs are uniformly `O(r^(-3/2))` in the amplitude. -/
theorem saddle_outer_integral_rank_error :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ r : ℕ, N ≤ r →
      ∀ d : ℝ, 0 ≤ d → d ≤ 1 →
      |(∫ θ in (-Real.pi)..(-Real.pi / 4), saddleRealKernel (saddleRadius r) d θ) +
        (∫ θ in (Real.pi / 4)..Real.pi, saddleRealKernel (saddleRadius r) d θ)| ≤
          C / (r : ℝ) ^ (3 / 2 : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_saddle_exp_le_inv_pow 2)
  refine ⟨2 * Real.pi, by positivity, max N 1, le_max_right _ _, ?_⟩
  intro r hr d hd0 hd1
  have hrN : N ≤ r := (le_max_left _ _).trans hr
  have hr1 : 1 ≤ r := (le_max_right _ _).trans hr
  have hrpos : 0 < r := by omega
  have hrreal : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hpow : (r : ℝ) ^ (3 / 2 : ℝ) ≤ (r : ℝ) ^ (2 : ℕ) := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le hrreal (by norm_num : (3 / 2 : ℝ) ≤ (2 : ℕ))
  have hdecay : Real.exp (-saddleRadius r / 16) ≤ 1 / (r : ℝ) ^ (3 / 2 : ℝ) :=
    (hN r hrN).trans (one_div_le_one_div_of_le (by positivity) hpow)
  calc
    _ ≤ 2 * Real.pi * Real.exp (-saddleRadius r / 16) :=
      saddle_outer_integral_bound (saddleRadius_pos r hrpos).le hd0 hd1
    _ ≤ 2 * Real.pi * (1 / (r : ℝ) ^ (3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hdecay (by positivity)
    _ = _ := by ring

/-- An explicit full-line Gaussian tail estimate. Splitting the exponential
on the complement of the central interval leaves a fixed integrable Gaussian.
The bound is uniform in every `b ≥ t ≥ 1`. -/
theorem gaussian_tail_integral_bound {a b t : ℝ} (ha : 0 < a)
    (hb1 : 1 ≤ b) (_ht1 : 1 ≤ t) (htb : t ≤ b) :
    |(∫ θ : ℝ, Real.exp (-b * θ ^ 2 / 2)) -
      (∫ θ in (-a)..a, Real.exp (-b * θ ^ 2 / 2))| ≤
        Real.exp (-t * a ^ 2 / 4) * Real.sqrt (4 * Real.pi) := by
  let g : ℝ → ℝ := fun θ => Real.exp (-b * θ ^ 2 / 2)
  have hgi : Integrable g := by
    convert integrable_exp_neg_mul_sq (b := b / 2) (by linarith) using 1
    ext θ
    dsimp [g]
    congr 1
    ring
  have hmajor : Integrable (fun θ : ℝ =>
      Real.exp (-t * a ^ 2 / 4) * Real.exp (-(1 / 4 : ℝ) * θ ^ 2)) :=
    (integrable_exp_neg_mul_sq (b := (1 / 4 : ℝ)) (by norm_num)).const_mul _
  have hpoint (θ : ℝ) (hθ : θ ∈ (Set.Ioc (-a) a)ᶜ) :
      g θ ≤ Real.exp (-t * a ^ 2 / 4) * Real.exp (-(1 / 4 : ℝ) * θ ^ 2) := by
    have hout : θ ≤ -a ∨ a < θ := by
      simpa only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] using hθ
    have habs : a ≤ |θ| := by
      rcases hout with h | h
      · linarith [neg_le_abs θ]
      · exact h.le.trans (le_abs_self θ)
    have hsq : a ^ 2 ≤ θ ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ ha.le habs 2
    have hfirst := mul_le_mul htb hsq (sq_nonneg a) (show 0 ≤ b by linarith)
    have hsecond := mul_le_mul_of_nonneg_right hb1 (sq_nonneg θ)
    change Real.exp (-b * θ ^ 2 / 2) ≤ _
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have heq : (∫ θ, g θ) - (∫ θ in (-a)..a, g θ) =
      ∫ θ in (Set.Ioc (-a) a)ᶜ, g θ := by
    rw [intervalIntegral.integral_of_le (by linarith : -a ≤ a),
      ← setIntegral_compl measurableSet_Ioc hgi]
  change |(∫ θ, g θ) - (∫ θ in (-a)..a, g θ)| ≤ _
  rw [heq, abs_of_nonneg (integral_nonneg (fun θ => (Real.exp_pos _).le))]
  calc
    _ ≤ ∫ θ in (Set.Ioc (-a) a)ᶜ,
        Real.exp (-t * a ^ 2 / 4) * Real.exp (-(1 / 4 : ℝ) * θ ^ 2) :=
      setIntegral_mono_on hgi.integrableOn hmajor.integrableOn measurableSet_Ioc.compl hpoint
    _ ≤ ∫ θ : ℝ, Real.exp (-t * a ^ 2 / 4) * Real.exp (-(1 / 4 : ℝ) * θ ^ 2) :=
      setIntegral_le_integral hmajor (Eventually.of_forall (fun _ => by positivity))
    _ = _ := by
      rw [integral_const_mul, integral_gaussian]
      congr 2
      ring

/-- The comparison Gaussian's full-line integral differs from its fixed
central arc by `O(r^(-3/2))`, with a proved common threshold. -/
theorem saddleGaussian_tail_rank_error :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ r : ℕ, N ≤ r →
      |(∫ θ : ℝ, saddleGaussian (saddleRadius r) θ) -
        (∫ θ in (-Real.pi / 4)..(Real.pi / 4), saddleGaussian (saddleRadius r) θ)| ≤
          C / (r : ℝ) ^ (3 / 2 : ℝ) := by
  have hc : 0 < (Real.pi / 4) ^ 2 / 4 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_exp_neg_mul_le_inv_rpow hc (3 / 2))
  refine ⟨Real.sqrt (4 * Real.pi), by positivity, max N 1, le_max_right _ _, ?_⟩
  intro r hr
  have hrN : N ≤ r := (le_max_left _ _).trans hr
  have hr1 : 1 ≤ r := (le_max_right _ _).trans hr
  have hrpos : 0 < r := by omega
  have hrreal : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hb := (saddleVariance_bounds r hrpos).1
  have ht := gaussian_tail_integral_bound (a := Real.pi / 4)
    (b := saddleVariance (saddleRadius r)) (t := (r : ℝ))
    (by positivity) (hrreal.trans hb) hrreal hb
  have hdecay : Real.exp (-(r : ℝ) * (Real.pi / 4) ^ 2 / 4) ≤
      1 / (r : ℝ) ^ (3 / 2 : ℝ) := by
    convert hN r hrN using 1
    congr 1
    ring
  calc
    _ ≤ Real.exp (-(r : ℝ) * (Real.pi / 4) ^ 2 / 4) * Real.sqrt (4 * Real.pi) := by
      simpa only [saddleGaussian, neg_div] using ht
    _ ≤ (1 / (r : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (4 * Real.pi) :=
      mul_le_mul_of_nonneg_right hdecay (Real.sqrt_nonneg _)
    _ = _ := by ring

end SymmetricSubgroupAsymptotics
