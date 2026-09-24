import SymmetricSubgroupAsymptotics.SaddleKernel
import SymmetricSubgroupAsymptotics.AsymptoticTransfer
import SymmetricSubgroupAsymptotics.SaddleTails
import SymmetricSubgroupAsymptotics.SaddleCentral

/-! Normalization and assembly of the saddle integral estimates. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace SymmetricSubgroupAsymptotics

theorem integral_saddleGaussian (ρ : ℝ) :
    (∫ θ : ℝ, saddleGaussian ρ θ) =
      Real.sqrt (2 * Real.pi / saddleVariance ρ) := by
  simp_rw [saddleGaussian, show ∀ θ : ℝ,
    -(saddleVariance ρ) * θ ^ 2 / 2 = -(saddleVariance ρ / 2) * θ ^ 2
    from fun θ => by ring]
  rw [integral_gaussian]
  congr 1
  ring

theorem saddleGaussian_normalization {ρ : ℝ} (hb : 0 < saddleVariance ρ) :
    Real.sqrt (2 * Real.pi * saddleVariance ρ) / (2 * Real.pi) *
      (∫ θ : ℝ, saddleGaussian ρ θ) = 1 := by
  rw [integral_saddleGaussian]
  have hp : 0 < 2 * Real.pi := by positivity
  have hs : Real.sqrt (2 * Real.pi * saddleVariance ρ) *
      Real.sqrt (2 * Real.pi / saddleVariance ρ) = 2 * Real.pi := by
    apply (sq_eq_sq₀ (by positivity) hp.le).mp
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    field_simp
  calc
    _ = (Real.sqrt (2 * Real.pi * saddleVariance ρ) *
        Real.sqrt (2 * Real.pi / saddleVariance ρ)) / (2 * Real.pi) := by ring
    _ = 1 := by rw [hs, div_self hp.ne']

theorem saddle_normalizer_bound (r : ℕ) (hr : 0 < r) :
    Real.sqrt (2 * Real.pi * saddleVariance (saddleRadius r)) / (2 * Real.pi) ≤
      2 * Real.sqrt (r : ℝ) := by
  have hbound := (saddleVariance_bounds r hr).2
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hp : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    calc
      2 * Real.pi * saddleVariance (saddleRadius r) ≤
          8 * Real.pi * (r : ℝ) := by nlinarith [Real.pi_pos]
      _ ≤ (2 * Real.sqrt (r : ℝ) * (2 * Real.pi)) ^ 2 := by
        simp only [mul_pow, Real.sq_sqrt hrpos.le]
        nlinarith [mul_nonneg (sub_nonneg.mpr hp) hrpos.le,
          mul_nonneg (sub_nonneg.mpr hp) (by positivity : 0 ≤ Real.pi * (r : ℝ))]

theorem normalizedSaddleIntegral_error_of_integral_bound
    (r : ℕ) (hr : 0 < r) (d C : ℝ) (hC : 0 ≤ C)
    (herror : |(∫ θ in (-Real.pi)..Real.pi,
        saddleRealKernel (saddleRadius r) d θ) -
        ∫ θ : ℝ, saddleGaussian (saddleRadius r) θ| ≤
      C / ((r : ℝ) * Real.sqrt (r : ℝ))) :
    |normalizedSaddleIntegral (saddleRadius r) d - 1| ≤ 2 * C / (r : ℝ) := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hspos : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr hrpos
  have hb := saddleVariance_saddleRadius_pos r hr
  rw [normalizedSaddleIntegral, ← saddleGaussian_normalization hb, ← mul_sub, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤
      Real.sqrt (2 * Real.pi * saddleVariance (saddleRadius r)) / (2 * Real.pi))]
  calc
    _ ≤ (Real.sqrt (2 * Real.pi * saddleVariance (saddleRadius r)) / (2 * Real.pi)) *
        (C / ((r : ℝ) * Real.sqrt (r : ℝ))) :=
      mul_le_mul_of_nonneg_left herror (by positivity)
    _ ≤ (2 * Real.sqrt (r : ℝ)) * (C / ((r : ℝ) * Real.sqrt (r : ℝ))) :=
      mul_le_mul_of_nonneg_right (saddle_normalizer_bound r hr) (by positivity)
    _ = 2 * C / (r : ℝ) := by field_simp

/-- The real three-halves power, including the value at zero. -/
theorem rpow_three_halves (x : ℝ) (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  by_cases hx0 : x = 0
  · subst x
    norm_num
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add hxpos, Real.rpow_one, Real.sqrt_eq_rpow]

private theorem abs_three_arc_comparison (a b c u v : ℝ) :
    |a + b + c - v| ≤ |a + c| + |b - u| + |v - u| := by
  have h1 := abs_add_le (a + c) (b - u)
  have h2 := abs_add_le ((a + c) + (b - u)) (u - v)
  have hswap := abs_sub_comm u v
  rw [show a + b + c - v = (a + c) + (b - u) + (u - v) by ring]
  linarith

/-- The complete circle integral is close to the whole-line Gaussian.
The central approximation and both actual tails are all included. -/
theorem saddle_integral_rank_error :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ r : ℕ, N ≤ r →
      ∀ d : ℝ, 0 ≤ d → d ≤ 1 →
      |(∫ θ in (-Real.pi)..Real.pi, saddleRealKernel (saddleRadius r) d θ) -
        ∫ θ : ℝ, saddleGaussian (saddleRadius r) θ| ≤
          C / ((r : ℝ) * Real.sqrt (r : ℝ)) := by
  obtain ⟨Co, hCo, No, hNo, ho⟩ := saddle_outer_integral_rank_error
  obtain ⟨Cg, hCg, Ng, _, hg⟩ := saddleGaussian_tail_rank_error
  refine ⟨Co + 134217728 + Cg, by positivity, max No Ng,
    hNo.trans (le_max_left _ _), ?_⟩
  intro r hr d hd0 hd1
  have hrNo : No ≤ r := (le_max_left _ _).trans hr
  have hrNg : Ng ≤ r := (le_max_right _ _).trans hr
  have hrpos : 0 < r := lt_of_lt_of_le (by omega : 0 < No) hrNo
  have houter := ho r hrNo d hd0 hd1
  have hgaussian := hg r hrNg
  rw [rpow_three_halves (r : ℝ) (Nat.cast_nonneg r)] at houter hgaussian
  have hcentral := saddleCentral_integral_error r hrpos hd0 hd1
  let H : ℝ → ℝ := saddleRealKernel (saddleRadius r) d
  let G : ℝ → ℝ := saddleGaussian (saddleRadius r)
  have hH : Continuous H := continuous_saddleRealKernel (saddleRadius r) d
  have hsplit : (∫ θ in (-Real.pi)..Real.pi, H θ) =
      (∫ θ in (-Real.pi)..(-Real.pi / 4), H θ) +
      (∫ θ in (-Real.pi / 4)..(Real.pi / 4), H θ) +
      (∫ θ in (Real.pi / 4)..Real.pi, H θ) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hH.intervalIntegrable (μ := volume) (-Real.pi) (-Real.pi / 4))
      (hH.intervalIntegrable (μ := volume) (-Real.pi / 4) Real.pi)
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hH.intervalIntegrable (μ := volume) (-Real.pi / 4) (Real.pi / 4))
      (hH.intervalIntegrable (μ := volume) (Real.pi / 4) Real.pi)
    linarith
  have htriangle := abs_three_arc_comparison
    (∫ θ in (-Real.pi)..(-Real.pi / 4), H θ)
    (∫ θ in (-Real.pi / 4)..(Real.pi / 4), H θ)
    (∫ θ in (Real.pi / 4)..Real.pi, H θ)
    (∫ θ in (-Real.pi / 4)..(Real.pi / 4), G θ)
    (∫ θ : ℝ, G θ)
  rw [← hsplit] at htriangle
  calc
    _ ≤ _ := htriangle
    _ ≤ Co / ((r : ℝ) * Real.sqrt (r : ℝ)) +
        134217728 / ((r : ℝ) * Real.sqrt (r : ℝ)) +
        Cg / ((r : ℝ) * Real.sqrt (r : ℝ)) :=
      add_le_add (add_le_add houter hcentral) hgaussian
    _ = _ := by ring

/-- Uniform quantified saddle accuracy for every amplitude in `[0,1]`.
This is a closed estimate for the normalized analytic integral; identifying
it with the coefficient benchmark is a separate coefficient-extraction step. -/
theorem normalizedSaddleIntegral_rank_error :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ r : ℕ, N ≤ r →
      ∀ d : ℝ, 0 ≤ d → d ≤ 1 →
      |normalizedSaddleIntegral (saddleRadius r) d - 1| ≤ C / (r : ℝ) := by
  obtain ⟨C, hC, N, hN, h⟩ := saddle_integral_rank_error
  refine ⟨2 * C, by positivity, N, hN, ?_⟩
  intro r hr d hd0 hd1
  exact normalizedSaddleIntegral_error_of_integral_bound r
    (lt_of_lt_of_le (by omega : 0 < N) hr) d C hC.le (h r hr d hd0 hd1)

end SymmetricSubgroupAsymptotics
