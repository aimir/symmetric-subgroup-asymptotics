import SymmetricSubgroupAsymptotics.TerminalGaussian

/-!
# Uniform and endpoint-sensitive terminal ratios

Every rank in both finite sums is included. These numerical estimates do not
assert the still separate incidence bound for actual terminal subgroups.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

private theorem terminal_sum_of_term_bound (r c d τ : ℕ) (w : ℕ → ℝ)
    (h : ∀ j ≤ r, ∀ l ≤ c,
      (binaryGaussianCoefficient c l : ℝ) * (72 : ℝ)^l *
        (2 : ℝ)^((τ : ℝ)*l + ((j : ℝ)-l)*((r : ℝ)-j+d)) ≤
          eulerProduct⁻¹ * terminalGaussianWeight r d * w l) :
    terminalGaussianDoubleSum r c d τ ≤
      (eulerProduct⁻¹)^3 * (r+1) * terminalGaussianWeight r d *
        ∑ l ∈ Finset.range (c+1), w l := by
  unfold terminalGaussianDoubleSum
  calc
    _ ≤ (eulerProduct⁻¹)^2 * ∑ j ∈ Finset.range (r+1),
        ∑ l ∈ Finset.range (c+1), eulerProduct⁻¹ * terminalGaussianWeight r d * w l := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro l hl
      exact h j (by simpa using hj) l (by simpa using hl)
    _ = _ := by
      simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]
      ring

/-- The complete endpoint ratio. The extra suppression for large exterior
rank is retained in its exact exponent. -/
theorem terminalGaussianDoubleSum_endpoint_le (r c d τ : ℕ) (hd : r ≤ d) :
    terminalGaussianDoubleSum r c d τ ≤
      (eulerProduct⁻¹)^3 * (r+1) * terminalGaussianWeight r d *
        ∑ l ∈ Finset.range (c+1), terminalEndpointRelationWeight c d τ l :=
  terminal_sum_of_term_bound r c d τ _
    (fun j hj l hl => terminalGaussian_term_endpoint_le r c d τ j l hd hj hl)

/-- One bound covers both interior and endpoint regimes, with explicit
absolute constant and the full retained relation-dimension sum. -/
theorem terminalGaussianDoubleSum_le (r c d τ : ℕ) :
    terminalGaussianDoubleSum r c d τ ≤
      2 * (eulerProduct⁻¹)^3 * (r+1) * terminalGaussianWeight r d *
        ∑ l ∈ Finset.range (c+1), terminalRelationWeight r c d τ l := by
  have h := terminal_sum_of_term_bound r c d τ
    (fun l => 2 * terminalRelationWeight r c d τ l) ?_
  · simpa only [← Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using h
  intro j hj l hl
  rcases le_total d r with hd | hd
  · simpa only [mul_assoc, mul_left_comm, mul_comm] using
      terminalGaussian_term_interior_le r c d τ j l hd hl
  · have hrel := terminalEndpointRelationWeight_le r c d τ l hd
    have hpos : 0 ≤ terminalRelationWeight r c d τ l := by
      unfold terminalRelationWeight
      positivity
    exact (terminalGaussian_term_endpoint_le r c d τ j l hd hj hl).trans
      (mul_le_mul_of_nonneg_left (hrel.trans (by linarith))
        (mul_nonneg (inv_nonneg.mpr euler_positive.le) (terminalGaussianWeight_pos r d).le))

theorem terminalGaussianDoubleSum_div_le (r c d τ : ℕ) :
    terminalGaussianDoubleSum r c d τ / terminalGaussianWeight r d ≤
      2 * (eulerProduct⁻¹)^3 * (r+1) *
        ∑ l ∈ Finset.range (c+1), terminalRelationWeight r c d τ l := by
  apply (div_le_iff₀ (terminalGaussianWeight_pos r d)).mpr
  simpa only [mul_assoc, mul_comm, mul_left_comm] using terminalGaussianDoubleSum_le r c d τ

theorem terminalGaussianDoubleSum_endpoint_div_le (r c d τ : ℕ) (hd : r ≤ d) :
    terminalGaussianDoubleSum r c d τ / terminalGaussianWeight r d ≤
      (eulerProduct⁻¹)^3 * (r+1) *
        ∑ l ∈ Finset.range (c+1), terminalEndpointRelationWeight c d τ l := by
  apply (div_le_iff₀ (terminalGaussianWeight_pos r d)).mpr
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    terminalGaussianDoubleSum_endpoint_le r c d τ hd

/-- A relation kernel on all nonnegative dimensions. -/
def terminalRelationKernel (a : ℝ) (l : ℕ) : ℝ :=
  (72 : ℝ)^l * (2 : ℝ)^(-(l : ℝ)*a-3*(l : ℝ)^2/4)

theorem terminalRelationKernel_geometric_bound (a : ℝ) (l : ℕ) :
    terminalRelationKernel a l ≤ (2 : ℝ)^((8-a)^2) * (1/2 : ℝ)^l := by
  have h72 : (72 : ℝ)^l ≤ (2 : ℝ)^(7*(l : ℝ)) := by
    calc
      _ ≤ ((2 : ℝ)^(7 : ℕ))^l := pow_le_pow_left₀ (by norm_num) (by norm_num) l
      _ = _ := by rw [← pow_mul, ← Real.rpow_natCast]; push_cast; rfl
  unfold terminalRelationKernel
  calc
    _ ≤ (2 : ℝ)^(7*(l : ℝ)) * (2 : ℝ)^(-(l : ℝ)*a-3*(l : ℝ)^2/4) :=
      mul_le_mul_of_nonneg_right h72 (by positivity)
    _ = (2 : ℝ)^(7*(l : ℝ) - (l : ℝ)*a-3*(l : ℝ)^2/4) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ (2 : ℝ)^((8-a)^2-(l : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [sq_nonneg ((l : ℝ)/2-(8-a)), sq_nonneg (l : ℝ)]
    _ = _ := by
      rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
      simp [div_eq_mul_inv, ← inv_pow]

theorem terminalRelationKernel_summable (a : ℝ) : Summable (terminalRelationKernel a) :=
  (summable_geometric_two.mul_left ((2 : ℝ)^((8-a)^2))).of_nonneg_of_le
    (fun l => by unfold terminalRelationKernel; positivity)
    (terminalRelationKernel_geometric_bound a)

/-- The finite relation-dimension bound may be extended to the entire
convergent series, including its zero-dimensional term. -/
theorem terminalGaussianDoubleSum_div_le_series (r c d τ : ℕ) :
    terminalGaussianDoubleSum r c d τ / terminalGaussianWeight r d ≤
      2 * (eulerProduct⁻¹)^3 * (r+1) *
        ∑' l : ℕ, terminalRelationKernel ((r : ℝ)/2-c+d/2-τ) l := by
  refine (terminalGaussianDoubleSum_div_le r c d τ).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity [euler_positive])
  simpa only [terminalRelationWeight, terminalRelationKernel, neg_mul] using
    (terminalRelationKernel_summable ((r : ℝ)/2-c+d/2-τ)).sum_le_tsum
      (Finset.range (c+1)) (fun l _ => by unfold terminalRelationKernel; positivity)

/-- With a nonnegative deficit, the relation sum has one absolute bound. -/
theorem terminalRelationKernel_tsum_le (a : ℝ) (ha : 0 ≤ a) :
    (∑' l : ℕ, terminalRelationKernel a l) ≤ (2 : ℝ)^(65 : ℕ) := by
  have hterm (l : ℕ) : terminalRelationKernel a l ≤
      (2 : ℝ)^(64 : ℕ) * (1/2 : ℝ)^l := by
    calc
      _ ≤ terminalRelationKernel 0 l := by
        unfold terminalRelationKernel
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have h := mul_nonneg (show (0 : ℝ) ≤ l by positivity) ha
        nlinarith
      _ ≤ _ := by
        have h := terminalRelationKernel_geometric_bound 0 l
        norm_num only [sub_zero, show (8 : ℝ)^2 = (64 : ℕ) by norm_num,
          Real.rpow_natCast] at h
        norm_num at h ⊢
        exact h
  calc
    _ ≤ ∑' l : ℕ, (2 : ℝ)^(64 : ℕ) * (1/2 : ℝ)^l :=
      (terminalRelationKernel_summable a).tsum_le_tsum hterm
        (summable_geometric_two.mul_left _)
    _ = _ := by rw [tsum_mul_left, tsum_geometric_two]; norm_num

/-- The inflation-kernel-free numerical terminal estimate is uniform in
every exterior rank and includes all zero-dimensional boundary cases. -/
theorem terminalGaussianDoubleSum_zero_inflation_le (r c d : ℕ) (hc : 2*c ≤ r) :
    terminalGaussianDoubleSum r c d 0 ≤
      ((2 : ℝ)^(66 : ℕ) * (eulerProduct⁻¹)^3) * (r+1) * terminalGaussianWeight r d := by
  have hgap : 0 ≤ (r : ℝ)/2-c+d/2-0 := by
    have hc' : 2*(c : ℝ) ≤ r := by exact_mod_cast hc
    have hd : (0 : ℝ) ≤ d := by positivity
    linarith
  have h := (terminalGaussianDoubleSum_div_le_series r c d 0).trans
    (mul_le_mul_of_nonneg_left (terminalRelationKernel_tsum_le _ (by simpa using hgap))
      (by positivity [euler_positive]))
  have h' := (div_le_iff₀ (terminalGaussianWeight_pos r d)).mp h
  calc
    _ ≤ _ := h'
    _ = _ := by
      rw [show (66 : ℕ) = 65+1 from rfl, pow_succ]
      ring

end SymmetricSubgroupAsymptotics
