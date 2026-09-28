import SymmetricSubgroupAsymptotics.GrowingQuotientColdAggregate

/-!
# The growing comparator cold forward row

Each removed width is assigned to its literal complement degree.  The row sum
is the exact sum of the width aggregates.  Their pointwise bounds form a
geometric series, giving the manuscript's factor-two aggregate with no loss
in the exponent.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {ι : ℕ → Type*} [∀ w, Fintype (ι w)]

/-- Sum of all cold certificates at widths from `w₀` through `n`. -/
def growingQuotientColdTotal (w₀ n : ℕ)
    (D : ∀ w, ι w → ℕ → ℝ) (A α : ∀ w, ι w → ℝ) : ℝ :=
  ∑ w ∈ Finset.Ico w₀ (n + 1),
    growingQuotientColdWidthSum (n - w) w (D w) (A w) (α w)

/-- Assign each actual width to its literal complement degree. -/
def growingQuotientColdRow (w₀ : ℕ)
    (D : ∀ w, ι w → ℕ → ℝ) (A α : ∀ w, ι w → ℝ)
    (n b : ℕ) : ℝ :=
  ∑ w ∈ Finset.Ico w₀ (n + 1),
    if b + w = n then
      growingQuotientColdWidthSum b w (D w) (A w) (α w)
    else 0

theorem growingQuotientColdRow_nonneg (w₀ : ℕ)
    (D : ∀ w, ι w → ℕ → ℝ) (A α : ∀ w, ι w → ℝ)
    (hD : ∀ w i b, 0 ≤ D w i b) (hA : ∀ w i, 0 < A w i)
    (n b : ℕ) :
    0 ≤ growingQuotientColdRow w₀ D A α n b := by
  unfold growingQuotientColdRow
  apply Finset.sum_nonneg
  intro w _
  split_ifs
  · exact growingQuotientColdWidthSum_nonneg b w (D w) (A w) (α w)
      (hD w) (hA w)
  · exact le_rfl

theorem growingQuotientColdRow_forward (w₀ : ℕ) (hw₀ : 1 ≤ w₀)
    (D : ∀ w, ι w → ℕ → ℝ) (A α : ∀ w, ι w → ℝ)
    {n b : ℕ} (hnb : n ≤ b) :
    growingQuotientColdRow w₀ D A α n b = 0 := by
  unfold growingQuotientColdRow
  apply Finset.sum_eq_zero
  intro w hw
  have hw0 : w₀ ≤ w := (Finset.mem_Ico.mp hw).1
  have hwn : w ≤ n := Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hw).2
  have hwpos : 1 ≤ w := hw₀.trans hw0
  have hne : b + w ≠ n := by omega
  exact if_neg hne

/-- Summing target degrees recovers every retained width exactly once. -/
theorem growingQuotientColdRow_sum (w₀ : ℕ) (hw₀ : 1 ≤ w₀)
    (D : ∀ w, ι w → ℕ → ℝ) (A α : ∀ w, ι w → ℝ) (n : ℕ) :
    (∑ b ∈ Finset.range n, growingQuotientColdRow w₀ D A α n b) =
      growingQuotientColdTotal w₀ n D A α := by
  unfold growingQuotientColdRow growingQuotientColdTotal
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  have hww := Finset.mem_Ico.mp hw
  have hwn : w ≤ n := by omega
  have hb : n - w < n := by omega
  rw [Finset.sum_eq_single (n - w)]
  · rw [if_pos (Nat.sub_add_cancel hwn)]
  · intro b _ hne
    by_cases h : b + w = n
    · exact False.elim (hne (by omega))
    · exact if_neg h
  · simp [hb]

/-- Weighted reindexing retains each literal complement degree exactly.
This is the identity used when local physical bounds are assembled into the
global forward recurrence. -/
theorem growingQuotientColdRow_weighted_sum (w₀ : ℕ) (hw₀ : 1 ≤ w₀)
    (D : ∀ w, ι w → ℕ → ℝ) (A α : ∀ w, ι w → ℝ)
    (a : ℕ → ℝ) (n : ℕ) :
    (∑ b ∈ Finset.range n,
      growingQuotientColdRow w₀ D A α n b * a b) =
      ∑ w ∈ Finset.Ico w₀ (n + 1),
        growingQuotientColdWidthSum (n - w) w (D w) (A w) (α w) *
          a (n - w) := by
  unfold growingQuotientColdRow
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  have hww := Finset.mem_Ico.mp hw
  have hwn : w ≤ n := by omega
  have hb : n - w < n := by omega
  rw [Finset.sum_eq_single (n - w)]
  · rw [if_pos (Nat.sub_add_cancel hwn)]
  · intro b _ hne
    rw [if_neg (show b + w ≠ n from fun h => hne (by omega))]
  · simp only [Finset.mem_range, hb, not_true_eq_false, false_implies]

/-- The geometric tail of the pointwise width bounds costs at most a factor
two once its ratio is at most one half. -/
theorem growingQuotientColdTotal_le
    {ρ : ℝ} (w₀ n : ℕ)
    (D : ∀ w, ι w → ℕ → ℝ) (A α : ∀ w, ι w → ℝ)
    (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8) (hw₀ : 3 ≤ w₀)
    (hD : ∀ w i b, 0 ≤ D w i b) (hA : ∀ w i, 0 < A w i)
    (hgap : ∀ w i,
      α w i ≤ (halfDegree w : ℝ) / 4 - ρ * w / 4)
    (hoverhead : ∀ w, w ∈ Finset.Ico w₀ (n + 1) →
      eulerProduct⁻¹ ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (w + 2)) *
          (2 : ℝ) ^ ((halfDegree w : ℝ) / 4 + 1 / 4) *
          (∑ i, D w i (n - w) / A w i) ≤
        (2 : ℝ) ^ (ρ * w * n / 16))
    (hratio : (2 : ℝ) ^ (-ρ * n / 8) ≤ 1 / 2) :
    growingQuotientColdTotal w₀ n D A α ≤
      2 * (2 : ℝ) ^ (-ρ * w₀ * n / 8) := by
  let x : ℝ := (2 : ℝ) ^ (-ρ * n / 8)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hx1 : x < 1 := hratio.trans_lt (by norm_num)
  have hwidth (w : ℕ) (hw : w ∈ Finset.Ico w₀ (n + 1)) :
      growingQuotientColdWidthSum (n - w) w (D w) (A w) (α w) ≤ x ^ w := by
    have hww := Finset.mem_Ico.mp hw
    have hwn : w ≤ n := by omega
    have hlocal := growingQuotientColdWidthSum_le n w (D w) (A w) (α w)
      hρ hρ8 (hw₀.trans hww.1) hwn (hD w) (hA w) (hgap w)
      (hoverhead w hw)
    apply hlocal.trans_eq
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hsum : growingQuotientColdTotal w₀ n D A α ≤
      ∑ w ∈ Finset.Ico w₀ (n + 1), x ^ w := by
    unfold growingQuotientColdTotal
    exact Finset.sum_le_sum fun w hw => hwidth w hw
  have hgeom := geom_sum_Ico_le_of_lt_one (x := x) (m := w₀) (n := n + 1) hx0 hx1
  have hden : (1 - x)⁻¹ ≤ 2 := by
    have hhalf : (1 / 2 : ℝ) ≤ 1 - x := by linarith
    have hpos : 0 < 1 - x := sub_pos.mpr hx1
    rw [inv_le_iff_one_le_mul₀' hpos]
    nlinarith
  calc
    _ ≤ ∑ w ∈ Finset.Ico w₀ (n + 1), x ^ w := hsum
    _ ≤ x ^ w₀ / (1 - x) := hgeom
    _ = x ^ w₀ * (1 - x)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ x ^ w₀ * 2 := mul_le_mul_of_nonneg_left hden (pow_nonneg hx0 _)
    _ = 2 * (2 : ℝ) ^ (-ρ * w₀ * n / 8) := by
      have hp : x ^ w₀ = (2 : ℝ) ^ (-ρ * w₀ * n / 8) := by
        dsimp [x]
        rw [← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      rw [hp]
      ring

/-- The exact forward row inherits the same geometric aggregate. -/
theorem growingQuotientColdRow_sum_le
    {ρ : ℝ} (w₀ n : ℕ)
    (D : ∀ w, ι w → ℕ → ℝ) (A α : ∀ w, ι w → ℝ)
    (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8) (hw₀ : 3 ≤ w₀)
    (hD : ∀ w i b, 0 ≤ D w i b) (hA : ∀ w i, 0 < A w i)
    (hgap : ∀ w i,
      α w i ≤ (halfDegree w : ℝ) / 4 - ρ * w / 4)
    (hoverhead : ∀ w, w ∈ Finset.Ico w₀ (n + 1) →
      eulerProduct⁻¹ ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (w + 2)) *
          (2 : ℝ) ^ ((halfDegree w : ℝ) / 4 + 1 / 4) *
          (∑ i, D w i (n - w) / A w i) ≤
        (2 : ℝ) ^ (ρ * w * n / 16))
    (hratio : (2 : ℝ) ^ (-ρ * n / 8) ≤ 1 / 2) :
    (∑ b ∈ Finset.range n, growingQuotientColdRow w₀ D A α n b) ≤
      2 * (2 : ℝ) ^ (-ρ * w₀ * n / 8) := by
  rw [growingQuotientColdRow_sum w₀ (by omega) D A α n]
  exact growingQuotientColdTotal_le w₀ n D A α hρ hρ8 hw₀ hD hA hgap
    hoverhead hratio

end SymmetricSubgroupAsymptotics

end
