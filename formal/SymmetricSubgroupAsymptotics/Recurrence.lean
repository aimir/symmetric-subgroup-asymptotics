import Mathlib

/-!
# Boundedness before decay for forward recurrences

The kernels in this file only use indices in `Finset.range n`, hence strictly
smaller indices. Eventual contraction first bounds the complete target
sequence. Decaying scalar terms and row sums can then be applied against
that bound. None of these abstract results proves a subgroup-count target
without the corresponding counting estimates.
-/

set_option autoImplicit false

open scoped BigOperators
open Filter

namespace SymmetricSubgroupAsymptotics

/-- A nonnegative finite row can be bounded against a uniform target bound. -/
theorem weighted_sum_le_row_mul {a k : ℕ → ℝ} {n : ℕ} {M : ℝ}
    (hk : ∀ m ∈ Finset.range n, 0 ≤ k m)
    (ha : ∀ m ∈ Finset.range n, a m ≤ M) :
    (∑ m ∈ Finset.range n, k m * a m) ≤ (∑ m ∈ Finset.range n, k m) * M := by
  calc
    (∑ m ∈ Finset.range n, k m * a m) ≤ ∑ m ∈ Finset.range n, k m * M :=
      Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_left (ha m hm) (hk m hm)
    _ = (∑ m ∈ Finset.range n, k m) * M := (Finset.sum_mul _ _ _).symm

/-- Strong induction gives a bound from an initial segment and a compatible
forcing bound. No convergence or boundedness of the target is assumed. -/
theorem recurrence_le_of_initial_bound
    {a forcing : ℕ → ℝ} {kernel : ℕ → ℕ → ℝ} {N : ℕ} {q M : ℝ}
    (hM : 0 ≤ M)
    (hinitial : ∀ n, n < N → a n ≤ M)
    (hkernel : ∀ n, N ≤ n → ∀ m ∈ Finset.range n, 0 ≤ kernel n m)
    (hforcing : ∀ n, N ≤ n → forcing n ≤ (1 - q) * M)
    (hrow : ∀ n, N ≤ n → (∑ m ∈ Finset.range n, kernel n m) ≤ q)
    (hrecurrence : ∀ n, N ≤ n →
      a n ≤ forcing n + ∑ m ∈ Finset.range n, kernel n m * a m) :
    ∀ n, a n ≤ M := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < N
    · exact hinitial n hn
    · have hN : N ≤ n := Nat.le_of_not_gt hn
      have hsum := weighted_sum_le_row_mul (hkernel n hN)
        (fun m hm => ih m (Finset.mem_range.mp hm))
      have hrowM := mul_le_mul_of_nonneg_right (hrow n hN) hM
      have hrec := hrecurrence n hN
      have hforce := hforcing n hN
      nlinarith

/-- Bounded forcing and an eventually contractive row bound yield a positive
uniform bound. The finite initial segment is included explicitly in the
construction, before any decaying-error conclusion is drawn. Nonnegativity
of the forcing is unnecessary; its upper bound suffices. -/
theorem bounded_of_eventual_row_contraction
    {a forcing : ℕ → ℝ} {kernel : ℕ → ℕ → ℝ} {N : ℕ} {B q : ℝ}
    (ha : ∀ n, 0 ≤ a n) (hB : 0 ≤ B) (hq : q < 1)
    (hkernel : ∀ n, N ≤ n → ∀ m ∈ Finset.range n, 0 ≤ kernel n m)
    (hforcing : ∀ n, N ≤ n → forcing n ≤ B)
    (hrow : ∀ n, N ≤ n → (∑ m ∈ Finset.range n, kernel n m) ≤ q)
    (hrecurrence : ∀ n, N ≤ n →
      a n ≤ forcing n + ∑ m ∈ Finset.range n, kernel n m * a m) :
    ∃ M : ℝ, 0 < M ∧ ∀ n, a n ≤ M := by
  let S : ℝ := ∑ n ∈ Finset.range N, a n
  let M : ℝ := S + B / (1 - q) + 1
  have hS : 0 ≤ S := Finset.sum_nonneg fun n _ => ha n
  have hgap : 0 < 1 - q := sub_pos.mpr hq
  have hfrac : 0 ≤ B / (1 - q) := div_nonneg hB hgap.le
  have hM : 0 < M := by dsimp [M]; linarith
  have hforceM : B ≤ (1 - q) * M := by
    have hcancel : B / (1 - q) * (1 - q) = B :=
      div_mul_cancel₀ B (ne_of_gt hgap)
    have hprod : 0 ≤ (1 - q) * S := mul_nonneg hgap.le hS
    dsimp [M]
    nlinarith
  refine ⟨M, hM, recurrence_le_of_initial_bound hM.le ?_ hkernel ?_ hrow hrecurrence⟩
  · intro n hn
    have hnS : a n ≤ S := Finset.single_le_sum (fun m _ => ha m)
      (Finset.mem_range.mpr hn)
    dsimp [M]
    linarith
  · intro n hn
    exact (hforcing n hn).trans hforceM

/-- After bounding the complete target sequence, a row estimate transfers
any scalar decay profile to the error, with an explicit constant. -/
theorem error_le_decay_profile
    {a k : ℕ → ℝ} {n : ℕ} {M e scalar row profile Cs Ck : ℝ}
    (hM : 0 ≤ M) (ha : ∀ m ∈ Finset.range n, a m ≤ M)
    (hk : ∀ m ∈ Finset.range n, 0 ≤ k m)
    (he : e ≤ scalar + ∑ m ∈ Finset.range n, k m * a m)
    (hscalar : scalar ≤ Cs * profile)
    (hrow : (∑ m ∈ Finset.range n, k m) ≤ row)
    (hrow_decay : row ≤ Ck * profile) :
    e ≤ (Cs + M * Ck) * profile := by
  have hsum := weighted_sum_le_row_mul hk ha
  have hrowM := mul_le_mul_of_nonneg_right (hrow.trans hrow_decay) hM
  nlinarith

/-- Vanishing forcing and row sums give a vanishing nonnegative error against
an already bounded complete target sequence. -/
theorem error_tendsto_zero_of_bounded_targets
    {a error scalar : ℕ → ℝ} {kernel : ℕ → ℕ → ℝ} {N : ℕ} {M : ℝ}
    (ha : ∀ n, a n ≤ M) (herror : ∀ n, 0 ≤ error n)
    (hkernel : ∀ n, N ≤ n → ∀ m ∈ Finset.range n, 0 ≤ kernel n m)
    (hrecurrence : ∀ n, N ≤ n →
      error n ≤ scalar n + ∑ m ∈ Finset.range n, kernel n m * a m)
    (hscalar : Tendsto scalar atTop (nhds 0))
    (hrow : Tendsto (fun n => ∑ m ∈ Finset.range n, kernel n m) atTop (nhds 0)) :
    Tendsto error atTop (nhds 0) := by
  have hupper : Tendsto (fun n => scalar n +
      (∑ m ∈ Finset.range n, kernel n m) * M) atTop (nhds 0) := by
    simpa using hscalar.add (hrow.mul_const M)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall herror
  · filter_upwards [eventually_ge_atTop N] with n hn
    exact (hrecurrence n hn).trans (add_le_add le_rfl
      (weighted_sum_le_row_mul (hkernel n hn) (fun m _ => ha m)))

/-- Exponential scalar and row estimates give a quantified exponential error
after the complete target sequence has been bounded. This is a conditional
assembly theorem, not a proof of any subgroup asymptotic. -/
theorem exponential_error_of_bounded_targets
    {a error scalar : ℕ → ℝ} {kernel : ℕ → ℕ → ℝ}
    {N : ℕ} {c Cs Ck : ℝ}
    (hc : 0 < c) (hCs : 0 < Cs) (hCk : 0 ≤ Ck)
    (hbounded : ∃ M : ℝ, 0 < M ∧ ∀ n, a n ≤ M)
    (hkernel : ∀ n, N ≤ n → ∀ m ∈ Finset.range n, 0 ≤ kernel n m)
    (hrecurrence : ∀ n, N ≤ n →
      error n ≤ scalar n + ∑ m ∈ Finset.range n, kernel n m * a m)
    (hscalar : ∀ n, N ≤ n → scalar n ≤ Cs * (2 : ℝ) ^ (-c * (n : ℝ)))
    (hrow : ∀ n, N ≤ n →
      (∑ m ∈ Finset.range n, kernel n m) ≤ Ck * (2 : ℝ) ^ (-c * (n : ℝ))) :
    ∃ c' K : ℝ, 0 < c' ∧ 0 < K ∧ ∀ n, N ≤ n →
      error n ≤ K * (2 : ℝ) ^ (-c' * (n : ℝ)) := by
  obtain ⟨M, hM, ha⟩ := hbounded
  refine ⟨c, Cs + M * Ck, hc, by positivity, ?_⟩
  intro n hn
  exact error_le_decay_profile hM.le (fun m _ => ha m) (hkernel n hn)
    (hrecurrence n hn) (hscalar n hn) (hrow n hn) le_rfl

end SymmetricSubgroupAsymptotics
