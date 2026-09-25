import SymmetricSubgroupAsymptotics.ElementaryClassical
import SymmetricSubgroupAsymptotics.SaddleEstimates

/-!
# Exact residue normalization and the parity shift

The rank-based logarithmic model is compared with the approved elementary
benchmark. The even-degree comparison is exact; only the shift from `n-1`
to `n` contributes an error in odd degree.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The fourth-root scale appearing in the elementary expression. -/
def elementaryScale (n : ℕ) : ℝ := (48 * (n : ℝ)) ^ (1 / 4 : ℝ)

theorem elementaryScale_nonneg (n : ℕ) : 0 ≤ elementaryScale n := by
  unfold elementaryScale
  positivity

theorem elementaryScale_pos (n : ℕ) (hn : 0 < n) : 0 < elementaryScale n := by
  unfold elementaryScale
  positivity

theorem elementaryScale_pow_four (n : ℕ) : elementaryScale n ^ 4 = 48 * (n : ℝ) := by
  unfold elementaryScale
  rw [← Real.rpow_mul_natCast (by positivity) (1 / 4 : ℝ) 4]
  norm_num

theorem elementaryScale_sq (n : ℕ) :
    elementaryScale n ^ 2 / 6 = 2 * Real.sqrt ((n : ℝ) / 3) := by
  have hp := elementaryScale_pow_four n
  have hs := Real.sq_sqrt (show 0 ≤ (n : ℝ) / 3 by positivity)
  have heq : elementaryScale n ^ 2 = 12 * Real.sqrt ((n : ℝ) / 3) := by
    apply (sq_eq_sq₀ (sq_nonneg _) (by positivity)).mp
    nlinarith
  linarith

/-- The Gaussian exponent with the rank-parity correction displayed. -/
theorem gaussianPower_quadratic (r : ℕ) :
    (gaussianPower r : ℝ) = ((r : ℝ) ^ 2 - (r % 2 : ℕ)) / 4 := by
  have hsub : r - r / 2 = r / 2 + r % 2 := by omega
  have hr : (r : ℝ) = 2 * ((r / 2 : ℕ) : ℝ) + (r % 2 : ℕ) := by
    exact_mod_cast (show r = 2 * (r / 2) + r % 2 by omega)
  have hbit : r % 2 = 0 ∨ r % 2 = 1 := by omega
  have hbit2 : ((r % 2 : ℕ) : ℝ) ^ 2 = (r % 2 : ℕ) := by
    rcases hbit with h | h <;> norm_num [h]
  unfold gaussianPower
  rw [hsub]
  push_cast
  rw [hr]
  nlinarith

/-- Exact logarithm of the four approved residue constants, with the rank
parity and the degree parity kept distinct. -/
theorem log_residueConstant (n : ℕ) :
    Real.log (residueConstant n) = -(4 / 3 : ℝ) + Real.log (gaussianKappa (halfDegree n)) +
      (parity n : ℝ) * ((3 / 8 : ℝ) * Real.log 48 - Real.log 6) -
      (1 / 2 - (parity n : ℝ) / 16 + ((halfDegree n % 2 : ℕ) : ℝ) / 4) * Real.log 2 := by
  have hk0 := kappaEven_pos
  have hk1 := kappaOdd_pos
  have he : parity n = (n % 4) % 2 := by unfold parity; omega
  have hh : halfDegree n % 2 = (n % 4) / 2 := by unfold halfDegree; omega
  have hm : n % 4 < 4 := Nat.mod_lt n (by decide)
  interval_cases h : n % 4 <;>
    simp (disch := positivity) [residueConstant, gaussianKappa, he, hh, h,
      Real.log_mul, Real.log_div, Real.log_rpow] <;> ring_nf <;> simp_all

/-- Exact logarithmic form of the elementary benchmark, before the parity
shift from the rank scale is estimated. -/
theorem log_elementaryBenchmark (n : ℕ) (hn : 0 < n) :
    Real.log (elementaryBenchmark n) = Real.log (residueConstant n) +
      (3 * (parity n : ℝ) / 8) * Real.log n + ((n : ℝ) ^ 2 / 16) * Real.log 2 +
      ((n : ℝ) / 8) * (7 * Real.log n - Real.log 48 - (parity n : ℝ) * Real.log 2 - 7) +
      2 * Real.sqrt ((n : ℝ) / 3) + elementaryScale n / 2 := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc := residue_positive n
  unfold elementaryBenchmark elementaryScale
  rw [if_neg (Nat.ne_of_gt hn)]
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_rpow hn', Real.log_rpow (by norm_num : (0 : ℝ) < 2),
    Real.log_rpow (by positivity), Real.log_exp,
    Real.log_div (by positivity) (by positivity), Real.log_pow,
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp]
  ring

/-- The logarithmic model obtained from the quantitative factorial,
Gaussian-sum, amplitude, saddle-action and variance expansions. -/
def elementaryLogModel (n : ℕ) : ℝ :=
  let r := halfDegree n
  let e := parity n
  let x := saddleScale r
  (((n : ℝ) + 1 / 2) * Real.log n - n + (1 / 2) * Real.log (2 * Real.pi)) +
    (gaussianPower r : ℝ) * Real.log 2 + Real.log (gaussianKappa r) +
    (e : ℝ) * (Real.log (x / 6) + 6 / x) +
    ((r : ℝ) / 4 - r * Real.log x + x ^ 2 / 6 + x / 2 - 4 / 3 - 4 / x) -
    (1 / 2) * Real.log (8 * Real.pi * r)

/-- The exact parity-shift identity. In even degree every term on the right
vanishes. In odd degree it isolates a logarithmic difference and differences
between two fourth-root scales whose fourth powers differ by exactly 48. -/
theorem elementaryLogModel_difference (n : ℕ) (hn : 2 ≤ n) :
    elementaryLogModel n - Real.log (elementaryBenchmark n) - firstCorrection n =
      ((n : ℝ) - 3 * (parity n : ℝ) + 4) / 8 *
        (Real.log n - Real.log ((n : ℝ) - parity n)) - (parity n : ℝ) / 8 +
      (saddleScale (halfDegree n) ^ 2 - elementaryScale n ^ 2) / 6 +
      (saddleScale (halfDegree n) - elementaryScale n) / 2 +
      (6 * (parity n : ℝ) - 4) *
        (1 / saddleScale (halfDegree n) - 1 / elementaryScale n) := by
  have hn0 : 0 < n := by omega
  have hr0 : 0 < halfDegree n := by unfold halfDegree; omega
  have hx := saddleScale_pos (halfDegree n) hr0
  have hr : (halfDegree n : ℝ) = ((n : ℝ) - parity n) / 2 := by
    have h : 2 * halfDegree n + parity n = n := by unfold halfDegree parity; omega
    have h' : 2 * (halfDegree n : ℝ) + (parity n : ℝ) = n := by exact_mod_cast h
    linarith
  have ht : 0 < (n : ℝ) - parity n := by
    have h : 0 < (halfDegree n : ℝ) := by exact_mod_cast hr0
    linarith
  have hlogx : Real.log (saddleScale (halfDegree n)) =
      (Real.log 48 + Real.log ((n : ℝ) - parity n)) / 4 := by
    unfold saddleScale
    rw [show 96 * (halfDegree n : ℝ) = 48 * ((n : ℝ) - parity n) by linarith,
      Real.log_rpow (by positivity), Real.log_mul (by norm_num) ht.ne']
    ring
  have hlognorm : Real.log (8 * Real.pi * (halfDegree n : ℝ)) =
      2 * Real.log 2 + Real.log Real.pi + Real.log ((n : ℝ) - parity n) := by
    rw [show 8 * Real.pi * (halfDegree n : ℝ) =
      (2 : ℝ) ^ 2 * Real.pi * ((n : ℝ) - parity n) by rw [hr]; ring,
      Real.log_mul (by positivity) ht.ne',
      Real.log_mul (by norm_num) Real.pi_ne_zero, Real.log_pow]
    norm_num
  have hlog2pi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) Real.pi_ne_zero
  unfold elementaryLogModel
  dsimp only
  rw [log_elementaryBenchmark n hn0, log_residueConstant, gaussianPower_quadratic,
    Real.log_div hx.ne' (by norm_num : (6 : ℝ) ≠ 0), hlogx, hlognorm, hlog2pi,
    ← elementaryScale_sq, hr]
  change _ - ((6 * (parity n : ℝ) - 4) / elementaryScale n) = _
  rcases parity_cases n with he | he <;>
    simp only [he, Nat.cast_zero, Nat.cast_one] <;> ring

theorem saddleScale_even_degree (n : ℕ) (he : parity n = 0) :
    saddleScale (halfDegree n) = elementaryScale n := by
  have hn : 2 * halfDegree n = n := by unfold halfDegree parity at *; omega
  have hn' : 2 * (halfDegree n : ℝ) = n := by exact_mod_cast hn
  unfold saddleScale elementaryScale
  congr 1
  linarith

/-- Even degrees have no parity-shift remainder at all. -/
theorem elementaryLogModel_even_exact (n : ℕ) (hn : 2 ≤ n) (he : parity n = 0) :
    elementaryLogModel n - Real.log (elementaryBenchmark n) - firstCorrection n = 0 := by
  rw [elementaryLogModel_difference n hn, saddleScale_even_degree n he, he]
  simp

private theorem odd_log_shift_bound {N : ℝ} (hN : 3 ≤ N) :
    0 ≤ (N + 1) / 8 * (Real.log N - Real.log (N - 1)) - 1 / 8 ∧
      (N + 1) / 8 * (Real.log N - Real.log (N - 1)) - 1 / 8 ≤
        1 / Real.sqrt N := by
  have hN0 : 0 < N := by linarith
  have hNm : 0 < N - 1 := by linarith
  have hratio : 0 < N / (N - 1) := div_pos hN0 hNm
  have hlog : Real.log N - Real.log (N - 1) = Real.log (N / (N - 1)) :=
    (Real.log_div hN0.ne' hNm.ne').symm
  have hlo : 1 / N ≤ Real.log N - Real.log (N - 1) := by
    have h := Real.one_sub_inv_le_log_of_pos hratio
    have heq : 1 - (N / (N - 1))⁻¹ = 1 / N := by field_simp; ring
    simpa only [heq, ← hlog] using h
  have hhi : Real.log N - Real.log (N - 1) ≤ 1 / (N - 1) := by
    have h := Real.log_le_sub_one_of_pos hratio
    have heq : N / (N - 1) - 1 = 1 / (N - 1) := by field_simp; ring
    simpa only [heq, ← hlog] using h
  have hmulL := mul_le_mul_of_nonneg_left hlo (show 0 ≤ (N + 1) / 8 by positivity)
  have hmulU := mul_le_mul_of_nonneg_left hhi (show 0 ≤ (N + 1) / 8 by positivity)
  have hidL : (N + 1) / 8 * (1 / N) - 1 / 8 = 1 / (8 * N) := by field_simp; ring
  have hidU : (N + 1) / 8 * (1 / (N - 1)) - 1 / 8 = 1 / (4 * (N - 1)) := by
    field_simp
    ring
  have hroot : Real.sqrt N ≤ N - 1 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith
    · nlinarith [mul_nonneg (sub_nonneg.mpr hN) hN0.le]
  have hrecip : 1 / (4 * (N - 1)) ≤ 1 / Real.sqrt N :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr hN0) (by linarith)
  constructor
  · have hp : 0 ≤ 1 / (8 * N) := by positivity
    linarith
  · linarith

private theorem odd_scale_shift_bound {N x y : ℝ} (hN : 3 ≤ N) (hx : 1 ≤ x)
    (hxy : x ≤ y) (hx4 : x ^ 4 = 48 * (N - 1)) (hy4 : y ^ 4 = 48 * N) :
    |(N + 1) / 8 * (Real.log N - Real.log (N - 1)) - 1 / 8 +
      (x ^ 2 - y ^ 2) / 6 + (x - y) / 2 + 2 * (1 / x - 1 / y)| ≤
        128 / Real.sqrt N := by
  have hN0 : 0 < N := by linarith
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := hx0.trans_le hxy
  have hroot0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hroot : Real.sqrt N ≤ x ^ 2 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg N) (sq_nonneg x)).mp
    rw [Real.sq_sqrt hN0.le]
    nlinarith
  have hsq : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx0.le hxy 2
  have hfour : (y ^ 2 - x ^ 2) * (y ^ 2 + x ^ 2) = 48 := by nlinarith
  have hprod : (y ^ 2 - x ^ 2) * x ^ 2 ≤ 48 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsq) (sq_nonneg y)]
  have hsqbound : y ^ 2 - x ^ 2 ≤ 48 / Real.sqrt N := by
    apply (le_div_iff₀ hroot0).mpr
    exact (mul_le_mul_of_nonneg_left hroot (sub_nonneg.mpr hsq)).trans hprod
  have hlinear : y - x ≤ y ^ 2 - x ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ y + x - 1 by linarith)]
  have hxy1 : 1 ≤ x * y := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (show 0 ≤ y - 1 by linarith)]
  have hinv0 : 0 ≤ 1 / x - 1 / y :=
    sub_nonneg.mpr (one_div_le_one_div_of_le hx0 hxy)
  have hinv : 1 / x - 1 / y ≤ y - x := by
    rw [show 1 / x - 1 / y = (y - x) / (x * y) by field_simp]
    apply (div_le_iff₀ (mul_pos hx0 hy0)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hxy1)]
  have hlog := odd_log_shift_bound hN
  have hrecip : 0 ≤ 1 / Real.sqrt N := by positivity
  simp only [div_eq_mul_inv] at hsqbound hlog hrecip hinv0 hinv ⊢
  apply abs_le.mpr
  constructor <;> nlinarith only [hsqbound, hlinear, hinv0, hinv, hlog.1, hlog.2, hrecip, hxy]

/-- An explicit, uniform bound for the complete parity-shift remainder. -/
theorem elementaryLogModel_error_bound (n : ℕ) (hn : 2 ≤ n) :
    |elementaryLogModel n - Real.log (elementaryBenchmark n) - firstCorrection n| ≤
      128 / Real.sqrt (n : ℝ) := by
  rcases parity_cases n with he | he
  · rw [elementaryLogModel_even_exact n hn he, abs_zero]
    positivity
  have hn3 : 3 ≤ n := by unfold parity at he; omega
  have hN : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hr0 : 0 < halfDegree n := by unfold halfDegree; omega
  have hr : 2 * halfDegree n + 1 = n := by unfold halfDegree parity at *; omega
  have hr' : 2 * (halfDegree n : ℝ) + 1 = n := by exact_mod_cast hr
  have hx4 : saddleScale (halfDegree n) ^ 4 = 48 * ((n : ℝ) - 1) := by
    rw [saddleScale_pow_four]
    linarith
  have hy4 := elementaryScale_pow_four n
  have hxy : saddleScale (halfDegree n) ≤ elementaryScale n := by
    apply (pow_le_pow_iff_left₀ (saddleScale_nonneg _) (elementaryScale_nonneg n)
      (show 4 ≠ 0 by decide)).mp
    rw [hx4, hy4]
    linarith
  have h := odd_scale_shift_bound hN (one_le_saddleScale _ hr0) hxy hx4 hy4
  rw [elementaryLogModel_difference n hn, he]
  push_cast
  convert h using 1
  congr 1
  ring

/-- The quantified parity comparison used by the elementary benchmark
assembly. Its constants and onset work for both parities and all residues. -/
theorem elementaryLogModel_error :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      |elementaryLogModel n - Real.log (elementaryBenchmark n) - firstCorrection n| ≤
        C / Real.sqrt (n : ℝ) :=
  ⟨128, by norm_num, 2, le_rfl, elementaryLogModel_error_bound⟩

end SymmetricSubgroupAsymptotics
