import SymmetricSubgroupAsymptotics.CoefficientBounds
import SymmetricSubgroupAsymptotics.GeneratingFunction
import SymmetricSubgroupAsymptotics.SaddleKernel

/-!
# Analytic evaluation of the critical generating function

The three exponential series are absolutely summable. Regrouping their
Cartesian product by weighted degree gives exactly the approved finite
coefficient sum, at every complex argument.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

private def tripleDegree (t : (ℕ × ℕ) × ℕ) : ℕ := t.1.1 + 2 * t.1.2 + 4 * t.2

private def tripleTerm (z : ℂ) (t : (ℕ × ℕ) × ℕ) : ℂ :=
  ((z / 2) ^ t.1.1 / (t.1.1.factorial : ℂ)) *
    ((z ^ 2 / 6) ^ t.1.2 / (t.1.2.factorial : ℂ)) *
      ((z ^ 4 / 384) ^ t.2 / (t.2.factorial : ℂ))

set_option maxHeartbeats 1000000 in
private theorem triple_hasSum (z : ℂ) :
    HasSum (tripleTerm z) (Complex.exp (criticalComplexPolynomial z)) := by
  let A : ℕ → ℂ := fun n ↦ (z / 2) ^ n / (n.factorial : ℂ)
  let B : ℕ → ℂ := fun n ↦ (z ^ 2 / 6) ^ n / (n.factorial : ℂ)
  let D : ℕ → ℂ := fun n ↦ (z ^ 4 / 384) ^ n / (n.factorial : ℂ)
  have hA : HasSum A (Complex.exp (z / 2)) := by
    simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp (z / 2)
  have hB : HasSum B (Complex.exp (z ^ 2 / 6)) := by
    simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp (z ^ 2 / 6)
  have hD : HasSum D (Complex.exp (z ^ 4 / 384)) := by
    simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp (z ^ 4 / 384)
  have hAn : Summable (fun n ↦ ‖A n‖) := NormedSpace.norm_expSeries_div_summable (z / 2)
  have hBn : Summable (fun n ↦ ‖B n‖) := NormedSpace.norm_expSeries_div_summable (z ^ 2 / 6)
  have hDn : Summable (fun n ↦ ‖D n‖) := NormedSpace.norm_expSeries_div_summable (z ^ 4 / 384)
  have hAB : HasSum (fun t : ℕ × ℕ ↦ A t.1 * B t.2)
      (Complex.exp (z / 2) * Complex.exp (z ^ 2 / 6)) :=
    HasSum.mul (f := A) (g := B) (s := Complex.exp (z / 2))
      (t := Complex.exp (z ^ 2 / 6)) hA hB
      (summable_mul_of_summable_norm (f := A) (g := B) hAn hBn)
  have hABn : Summable (fun t : ℕ × ℕ ↦ ‖A t.1 * B t.2‖) := hAn.mul_norm hBn
  have hABD : HasSum (fun t : (ℕ × ℕ) × ℕ ↦ (A t.1.1 * B t.1.2) * D t.2)
      ((Complex.exp (z / 2) * Complex.exp (z ^ 2 / 6)) * Complex.exp (z ^ 4 / 384)) :=
    HasSum.mul (f := fun t : ℕ × ℕ ↦ A t.1 * B t.2) (g := D)
      (s := Complex.exp (z / 2) * Complex.exp (z ^ 2 / 6))
      (t := Complex.exp (z ^ 4 / 384)) hAB hD (summable_mul_of_summable_norm
        (f := fun t : ℕ × ℕ ↦ A t.1 * B t.2) (g := D) hABn hDn)
  simpa only [A, B, D, tripleTerm, ← Complex.exp_add, criticalComplexPolynomial] using hABD

private theorem triple_fibre (z : ℂ) (r : ℕ) :
    (∑' t : tripleDegree ⁻¹' {r}, tripleTerm z t) =
      (criticalCoefficient r : ℂ) * z ^ r := by
  classical
  rw [tsum_subtype]
  let B := (Finset.range (r + 1) ×ˢ Finset.range (r + 1)) ×ˢ Finset.range (r + 1)
  have hfinite : (∑' t, (tripleDegree ⁻¹' {r}).indicator (tripleTerm z) t) =
      ∑ t ∈ B, (tripleDegree ⁻¹' {r}).indicator (tripleTerm z) t := by
    apply tsum_eq_sum
    intro t ht
    apply Set.indicator_of_notMem
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    intro hd
    apply ht
    simp only [B, Finset.mem_product, Finset.mem_range]
    dsimp [tripleDegree] at hd
    omega
  rw [hfinite]
  simp only [B, Finset.sum_product]
  unfold criticalCoefficient
  push_cast
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff, tripleDegree,
    tripleTerm]
  split_ifs with hdegree
  · push_cast
    rw [← hdegree]
    simp only [pow_add, pow_mul, div_pow]
    field_simp
  · simp

/-- The coefficient series evaluates to the actual complex exponential. -/
theorem criticalCoefficient_complex_hasSum (z : ℂ) :
    HasSum (fun r : ℕ ↦ (criticalCoefficient r : ℂ) * z ^ r)
      (Complex.exp (criticalComplexPolynomial z)) := by
  have h := (triple_hasSum z).tsum_fiberwise tripleDegree
  simpa only [triple_fibre] using h

/-- Analytic evaluation, stated as equality of the convergent sum. -/
theorem criticalCoefficient_complex_tsum (z : ℂ) :
    (∑' r : ℕ, (criticalCoefficient r : ℂ) * z ^ r) =
      Complex.exp (criticalComplexPolynomial z) :=
  (criticalCoefficient_complex_hasSum z).tsum_eq

/-- The coefficient of the parity amplitude at an independent rank parameter.
The guard retains the correct zero contribution at rank zero. -/
def analyticParityCoefficient (ε r : ℕ) : ℚ :=
  criticalCoefficient r + if ε = 1 ∧ 0 < r then criticalCoefficient (r - 1) / 6 else 0

@[simp] theorem analyticParityCoefficient_halfDegree (n : ℕ) :
    analyticParityCoefficient (parity n) (halfDegree n) = parityCoefficient n := rfl

private theorem shifted_critical_hasSum (z : ℂ) :
    HasSum (fun r : ℕ ↦
      (if 0 < r then (criticalCoefficient (r - 1) : ℂ) / 6 else 0) * z ^ r)
      ((z / 6) * Complex.exp (criticalComplexPolynomial z)) := by
  have h := (criticalCoefficient_complex_hasSum z).mul_left (z / 6)
  have hshift : HasSum (fun r : ℕ ↦
      (if 0 < r + 1 then (criticalCoefficient (r + 1 - 1) : ℂ) / 6 else 0) * z ^ (r + 1))
      ((z / 6) * Complex.exp (criticalComplexPolynomial z)) := by
    refine h.congr_fun fun r ↦ ?_
    simp only [Nat.zero_lt_succ, if_true, Nat.add_sub_cancel, pow_succ]
    ring
  have hbase := (hasSum_nat_add_iff (f := fun r : ℕ ↦
    (if 0 < r then (criticalCoefficient (r - 1) : ℂ) / 6 else 0) * z ^ r) 1).mp hshift
  simpa only [Finset.sum_range_one, Nat.lt_irrefl, if_false, zero_mul, add_zero] using hbase

/-- Entire evaluation with the exact parity amplitude, for both parities. -/
theorem analyticParityCoefficient_complex_hasSum (ε : ℕ) (hε : ε ≤ 1) (z : ℂ) :
    HasSum (fun r : ℕ ↦ (analyticParityCoefficient ε r : ℂ) * z ^ r)
      ((1 + z / 6) ^ ε * Complex.exp (criticalComplexPolynomial z)) := by
  interval_cases ε
  · simpa [analyticParityCoefficient] using criticalCoefficient_complex_hasSum z
  · have h := (criticalCoefficient_complex_hasSum z).add (shifted_critical_hasSum z)
    convert h using 1
    · funext r
      by_cases hr : 0 < r <;> simp [analyticParityCoefficient, hr]
      ring
    · simp [add_mul]

/-- The analytically evaluated series gives the scalar Taylor expansion. -/
theorem analyticParityCoefficient_hasFPowerSeriesAt (ε : ℕ) (hε : ε ≤ 1) :
    HasFPowerSeriesAt
      (fun z : ℂ ↦ (1 + z / 6) ^ ε * Complex.exp (criticalComplexPolynomial z))
      (FormalMultilinearSeries.ofScalars ℂ (fun r ↦ (analyticParityCoefficient ε r : ℂ))) 0 := by
  rw [hasFPowerSeriesAt_iff]
  apply Filter.Eventually.of_forall
  intro z
  simpa only [FormalMultilinearSeries.coeff_ofScalars, zero_add, smul_eq_mul, mul_comm]
    using analyticParityCoefficient_complex_hasSum ε hε z

end SymmetricSubgroupAsymptotics
