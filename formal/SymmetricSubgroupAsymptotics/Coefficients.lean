import SymmetricSubgroupAsymptotics.Foundations

/-!
# Exact identities for the critical coefficients

The finite rational formula satisfies the differential-equation recurrence
for the coefficients of exp(x/2 + x²/6 + x⁴/384). All index shifts below are
proved on finite sums, with absent negative indices treated explicitly.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

private def weight (a b d : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ a * (Nat.factorial a : ℚ) *
    6 ^ b * (Nat.factorial b : ℚ) * 384 ^ d * (Nat.factorial d : ℚ))

private def box (r A B D : ℕ) (w : ℕ → ℕ → ℕ → ℚ) : ℚ :=
  ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range B, ∑ d ∈ Finset.range D,
    if a + 2 * b + 4 * d = r then w a b d else 0

private theorem shrink_sum {f : ℕ → ℚ} {n m : ℕ} (hnm : n ≤ m)
    (hzero : ∀ i, n ≤ i → f i = 0) :
    (∑ i ∈ Finset.range m, f i) = ∑ i ∈ Finset.range n, f i := by
  symm
  apply Finset.sum_subset (Finset.range_mono hnm)
  intro i hi hni
  exact hzero i (by simpa using hni)

private theorem box_eq (r A B D : ℕ) (hA : r < A) (hB : r < B) (hD : r < D) :
    box r A B D weight = criticalCoefficient r := by
  unfold box criticalCoefficient
  rw [shrink_sum (Nat.succ_le_of_lt hA) (by
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    apply Finset.sum_eq_zero
    intro d hd
    exact if_neg (by omega))]
  apply Finset.sum_congr rfl
  intro a ha
  rw [shrink_sum (Nat.succ_le_of_lt hB) (by
    intro b hb
    apply Finset.sum_eq_zero
    intro d hd
    exact if_neg (by omega))]
  apply Finset.sum_congr rfl
  intro b hb
  rw [shrink_sum (Nat.succ_le_of_lt hD) (by
    intro d hd
    exact if_neg (by omega))]
  rfl

private theorem weight_first (a b d : ℕ) :
    ((a + 1 : ℕ) : ℚ) * weight (a + 1) b d = weight a b d / 2 := by
  simp only [weight, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    pow_succ]
  have ha : (a : ℚ) + 1 ≠ 0 := by positivity
  field_simp

private theorem weight_second (a b d : ℕ) :
    ((b + 1 : ℕ) : ℚ) * weight a (b + 1) d = weight a b d / 6 := by
  simp only [weight, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    pow_succ]
  have hb : (b : ℚ) + 1 ≠ 0 := by positivity
  field_simp

private theorem weight_fourth (a b d : ℕ) :
    ((d + 1 : ℕ) : ℚ) * weight a b (d + 1) = weight a b d / 384 := by
  simp only [weight, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    pow_succ]
  have hd : (d : ℚ) + 1 ≠ 0 := by positivity
  field_simp

private theorem moment_first (n : ℕ) :
    box (n + 4) (n + 5) (n + 5) (n + 5) (fun a b d => (a : ℚ) * weight a b d) =
      criticalCoefficient (n + 3) / 2 := by
  calc
    _ = box (n + 3) (n + 4) (n + 5) (n + 5) weight / 2 := by
      unfold box
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_mul, ite_self, Finset.sum_const_zero, add_zero]
      simp_rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro d hd
      simp only [show a + 1 + 2 * b + 4 * d = n + 4 ↔ a + 2 * b + 4 * d = n + 3 by omega]
      split_ifs
      · exact weight_first a b d
      · simp
    _ = _ := by rw [box_eq _ _ _ _ (by omega) (by omega) (by omega)]

private theorem moment_second (n : ℕ) :
    box (n + 4) (n + 5) (n + 5) (n + 5) (fun a b d => (b : ℚ) * weight a b d) =
      criticalCoefficient (n + 2) / 6 := by
  calc
    _ = box (n + 2) (n + 5) (n + 4) (n + 5) weight / 6 := by
      unfold box
      simp_rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_mul, ite_self, Finset.sum_const_zero, add_zero]
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro d hd
      simp only [show a + 2 * (b + 1) + 4 * d = n + 4 ↔ a + 2 * b + 4 * d = n + 2 by omega]
      split_ifs
      · exact weight_second a b d
      · simp
    _ = _ := by rw [box_eq _ _ _ _ (by omega) (by omega) (by omega)]

private theorem moment_fourth (n : ℕ) :
    box (n + 4) (n + 5) (n + 5) (n + 5) (fun a b d => (d : ℚ) * weight a b d) =
      criticalCoefficient n / 384 := by
  calc
    _ = box n (n + 5) (n + 5) (n + 4) weight / 384 := by
      unfold box
      simp_rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_mul, ite_self, add_zero]
      apply Finset.sum_congr rfl
      intro d hd
      simp only [show a + 2 * b + 4 * (d + 1) = n + 4 ↔ a + 2 * b + 4 * d = n by omega]
      split_ifs
      · exact weight_fourth a b d
      · simp
    _ = _ := by rw [box_eq _ _ _ _ (by omega) (by omega) (by omega)]

/-- Exact recurrence, with indices chosen so every displayed coefficient exists. -/
theorem criticalCoefficient_recurrence_add_four (n : ℕ) :
    ((n + 4 : ℕ) : ℚ) * criticalCoefficient (n + 4) =
      criticalCoefficient (n + 3) / 2 + criticalCoefficient (n + 2) / 3 +
        criticalCoefficient n / 96 := by
  have h : ((n + 4 : ℕ) : ℚ) * criticalCoefficient (n + 4) =
      box (n + 4) (n + 5) (n + 5) (n + 5) (fun a b d => (a : ℚ) * weight a b d) +
        2 * box (n + 4) (n + 5) (n + 5) (n + 5) (fun a b d => (b : ℚ) * weight a b d) +
        4 * box (n + 4) (n + 5) (n + 5) (n + 5) (fun a b d => (d : ℚ) * weight a b d) := by
    rw [← box_eq (n + 4) (n + 5) (n + 5) (n + 5) (by omega) (by omega) (by omega)]
    unfold box
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro d hd
    split_ifs with heq
    · have heq' : (a : ℚ) + 2 * b + 4 * d = (n + 4 : ℕ) := by exact_mod_cast heq
      rw [← heq']
      ring
    · ring
  rw [moment_first, moment_second, moment_fourth] at h
  linarith

/-- The recurrence at all positive ranks. The guards implement zero for
negative coefficient indices, rather than truncated natural subtraction. -/
theorem criticalCoefficient_recurrence (n : ℕ) :
    ((n + 1 : ℕ) : ℚ) * criticalCoefficient (n + 1) =
      criticalCoefficient n / 2 +
        (if 1 ≤ n then criticalCoefficient (n - 1) / 3 else 0) +
        (if 3 ≤ n then criticalCoefficient (n - 3) / 96 else 0) := by
  by_cases hn : 3 ≤ n
  · have h := criticalCoefficient_recurrence_add_four (n - 3)
    have h4 : n - 3 + 4 = n + 1 := by omega
    have h3 : n - 3 + 3 = n := by omega
    have h2 : n - 3 + 2 = n - 1 := by omega
    simpa [h4, h3, h2, hn, show 1 ≤ n by omega] using h
  · interval_cases n <;> norm_num [criticalCoefficient, Finset.sum_range_succ]

/-- The initial coefficient and recurrence determine the whole sequence. -/
theorem criticalCoefficient_unique {f : ℕ → ℚ} (hzero : f 0 = 1)
    (hrec : ∀ n, ((n + 1 : ℕ) : ℚ) * f (n + 1) = f n / 2 +
      (if 1 ≤ n then f (n - 1) / 3 else 0) +
      (if 3 ≤ n then f (n - 3) / 96 else 0)) : f = criticalCoefficient := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa using hzero
    | succ n =>
      have h1 : (if 1 ≤ n then f (n - 1) / 3 else 0) =
          (if 1 ≤ n then criticalCoefficient (n - 1) / 3 else 0) := by
        split_ifs with h
        · rw [ih _ (by omega)]
        · rfl
      have h3 : (if 3 ≤ n then f (n - 3) / 96 else 0) =
          (if 3 ≤ n then criticalCoefficient (n - 3) / 96 else 0) := by
        split_ifs with h
        · rw [ih _ (by omega)]
        · rfl
      have h := hrec n
      rw [ih n (by omega), h1, h3, ← criticalCoefficient_recurrence] at h
      exact (mul_left_cancel₀ (by positivity : ((n + 1 : ℕ) : ℚ) ≠ 0)) h

/-- A one-step coefficient ratio bound used in the counting estimates. -/
theorem criticalCoefficient_le_next (n : ℕ) :
    criticalCoefficient n ≤ 2 * (n + 1 : ℕ) * criticalCoefficient (n + 1) := by
  have h := criticalCoefficient_recurrence n
  have h1 : 0 ≤ (if 1 ≤ n then criticalCoefficient (n - 1) / 3 else 0) := by
    split_ifs
    · exact div_nonneg (criticalCoefficient_nonneg _) (by norm_num)
    · norm_num
  have h3 : 0 ≤ (if 3 ≤ n then criticalCoefficient (n - 3) / 96 else 0) := by
    split_ifs
    · exact div_nonneg (criticalCoefficient_nonneg _) (by norm_num)
    · norm_num
  linarith

/-- A uniform bound for any finite backwards coefficient shift. -/
theorem criticalCoefficient_shift_le (r h : ℕ) (hh : h ≤ r) :
    criticalCoefficient (r - h) ≤ (2 * (r : ℚ)) ^ h * criticalCoefficient r := by
  induction h with
  | zero => simp
  | succ h ih =>
    have hh' : h ≤ r := by omega
    have hstep := criticalCoefficient_le_next (r - h - 1)
    have hi := ih hh'
    have hc := criticalCoefficient_pos (r - h)
    have hidx : r - h - 1 + 1 = r - h := by omega
    have hidx' : r - h - 1 = r - (h + 1) := by omega
    rw [hidx, hidx'] at hstep
    have hcast : ((r - h : ℕ) : ℚ) ≤ r := by exact_mod_cast Nat.sub_le r h
    have hm := mul_le_mul_of_nonneg_left hi (by positivity : (0 : ℚ) ≤ 2 * r)
    rw [pow_succ]
    nlinarith

end SymmetricSubgroupAsymptotics
