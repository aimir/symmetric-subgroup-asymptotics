import SymmetricSubgroupAsymptotics.GrowingQuotientColdRow

/-!
# Hot aggregation for a growing comparator menu

The pointwise hot kernel retains a quarter of `ρ² n²` before lower-order
terms.  Uniform graph-degree bounds allocate one sixteenth to the coarse
subgroup estimate, and a direct bound on the remaining original weighted
menu mass allocates one further sixteenth.  The complete growing hot union is
therefore bounded by `2^(-ρ² n²/8)`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {ι : ℕ → Type*} [∀ w, Fintype (ι w)]

/-- Sum of the growing hot kernels over all retained widths and certificates. -/
def growingQuotientHotTotal (s : ℕ → ℝ) (w₀ n : ℕ)
    (D : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (v : ∀ w, ι w → ℕ) (η δ c : ∀ w, ι w → ℝ) : ℝ :=
  ∑ w ∈ Finset.Ico w₀ (n + 1), ∑ i,
    growingQuotientHotKernel s (n - w) w (v w i)
      (D w i (n - w)) (A w i) (η w i) (δ w i) (c w i)

theorem growingQuotientHotTotal_nonneg
    (s : ℕ → ℝ) (w₀ n : ℕ)
    (D : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (v : ∀ w, ι w → ℕ) (η δ c : ∀ w, ι w → ℝ)
    (hs : ∀ m, 0 ≤ s m)
    (hD : ∀ w i b, 0 ≤ D w i b) (hA : ∀ w i, 0 < A w i) :
    0 ≤ growingQuotientHotTotal s w₀ n D A v η δ c := by
  unfold growingQuotientHotTotal
  apply Finset.sum_nonneg
  intro w _
  apply Finset.sum_nonneg
  intro i _
  exact growingQuotientHotKernel_nonneg s (n - w) w (v w i)
    (hs _) (hD w i _) (hA w i)

/-- Complete growing-menu hot aggregation.  `hoverhead` is a direct bound on
the original certificate weights after the universal factorial polynomial;
it is the hot analogue of the cold-row mass interface. -/
theorem growingQuotientHotTotal_le
    (s : ℕ → ℝ) {ρ ε : ℝ} (w₀ n : ℕ)
    (D : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (v : ∀ w, ι w → ℕ) (η δ c : ∀ w, ι w → ℝ)
    (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8) (hε : 0 ≤ ε)
    (hD : ∀ w i b, 0 ≤ D w i b) (hA : ∀ w i, 0 < A w i)
    (hδ : ∀ w i, 0 ≤ δ w i) (hv : ∀ w i, 0 < v w i)
    (hratio : ∀ w i, ρ / 2 ≤ δ w i / (v w i : ℝ))
    (hvupper : ∀ w i, (v w i : ℝ) ≤ (1 - 4 * ρ) * w)
    (hδlower : ∀ w i, ρ * w / 2 ≤ δ w i)
    (hmargin : ∀ w i, η w i + c w i - w / 8 ≤ -δ w i / 2)
    (hc : ∀ w i, c w i = (v w i : ℝ) / 8 + δ w i / 2)
    (hδupper : ∀ w i, δ w i ≤ (w : ℝ) / 8)
    (hvlower : ∀ w i, ρ * w ≤ (v w i : ℝ))
    (hvwidth : ∀ w i, (v w i : ℝ) ≤ w)
    (hεbound : ε * (1 + 1 / (2 * ρ)) ^ 2 ≤ ρ ^ 2 / 16)
    (hs : ∀ w, w ∈ Finset.Ico w₀ (n + 1) → ∀ i,
      s (growingQuotientGraphDegree (δ w i) (n - w) (v w i)) ≤
        (2 : ℝ) ^ ((1 / 16 + ε) *
          (growingQuotientGraphDegree (δ w i) (n - w) (v w i) : ℝ) ^ 2))
    (hoverhead :
      eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ n) *
          (2 : ℝ) ^ (5 * (n : ℝ) / 8 + 1 / 4) *
          (∑ w ∈ Finset.Ico w₀ (n + 1), ∑ i, D w i (n - w) / A w i) ≤
        (2 : ℝ) ^ (ρ ^ 2 * (n : ℝ) ^ 2 / 16)) :
    growingQuotientHotTotal s w₀ n D A v η δ c ≤
      (2 : ℝ) ^ (-ρ ^ 2 * (n : ℝ) ^ 2 / 8) := by
  let L : ℝ := 1 + 1 / (2 * ρ)
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hentry (w : ℕ) (hw : w ∈ Finset.Ico w₀ (n + 1)) (i : ι w) :
      growingQuotientHotKernel s (n - w) w (v w i)
          (D w i (n - w)) (A w i) (η w i) (δ w i) (c w i) ≤
        (eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ n) *
          (D w i (n - w) / A w i)) *
            (2 : ℝ) ^ (-3 * ρ ^ 2 * (n : ℝ) ^ 2 / 16 +
              5 * (n : ℝ) / 8 + 1 / 4) := by
    have hww := Finset.mem_Ico.mp hw
    have hwn : w ≤ n := by omega
    have hn : n - w + w = n := Nat.sub_add_cancel hwn
    have hM := growingQuotientGraphDegree_upper (n - w) w (v w i)
      hρ (hδ w i) (hv w i) (hδupper w i) (hvlower w i) (hvwidth w i)
    have hM0 : 0 ≤
        (growingQuotientGraphDegree (δ w i) (n - w) (v w i) : ℝ) := by positivity
    have hMn :
        (growingQuotientGraphDegree (δ w i) (n - w) (v w i) : ℝ) ≤
          L * n := by
      have hbcast : ((n - w : ℕ) : ℝ) = (n : ℝ) - w := by
        rw [Nat.cast_sub hwn]
      dsimp [L] at hM ⊢
      rw [hbcast] at hM
      have hw0 : 0 ≤ (w : ℝ) := by positivity
      have hslope : 0 ≤ 1 / (2 * ρ) := by positivity
      nlinarith [mul_nonneg hslope hw0]
    have hcoarse :
        ε * (growingQuotientGraphDegree (δ w i) (n - w) (v w i) : ℝ) ^ 2 ≤
          ρ ^ 2 * (n : ℝ) ^ 2 / 16 := by
      exact growingQuotient_coarse_error_le hε hM0 hL0 (by positivity) hMn
        (by simpa only [L] using hεbound)
    have hhot := growingQuotientHotKernel_le
      (D := D w i (n - w)) (A := A w i) (ρ := ρ) (δ := δ w i)
      (η := η w i) (c := c w i) (ε := ε)
      s (n - w) w (v w i) (hD w i (n - w)) (hA w i)
      hρ hρ8 (hδ w i) (hv w i) (hratio w i) (hvupper w i)
      (hδlower w i) (hmargin w i) (hc w i) (hs w hw i)
    rw [hn] at hhot
    have hexp :
        -(ρ ^ 2) * (n : ℝ) ^ 2 / 4 +
            ε * (growingQuotientGraphDegree (δ w i) (n - w) (v w i) : ℝ) ^ 2 +
            5 * (n : ℝ) / 8 + 1 / 4 ≤
          -3 * ρ ^ 2 * (n : ℝ) ^ 2 / 16 + 5 * (n : ℝ) / 8 + 1 / 4 := by
      linarith
    exact hhot.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
      (mul_nonneg
        (mul_nonneg (inv_nonneg.mpr euler_positive.le) (by positivity))
        (div_nonneg (hD w i _) (hA w i).le)))
  have hsum : growingQuotientHotTotal s w₀ n D A v η δ c ≤
      (eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ n) *
        (∑ w ∈ Finset.Ico w₀ (n + 1), ∑ i, D w i (n - w) / A w i)) *
          (2 : ℝ) ^ (-3 * ρ ^ 2 * (n : ℝ) ^ 2 / 16 +
            5 * (n : ℝ) / 8 + 1 / 4) := by
    unfold growingQuotientHotTotal
    calc
      _ ≤ ∑ w ∈ Finset.Ico w₀ (n + 1), ∑ i,
          (eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ n) *
            (D w i (n - w) / A w i)) *
              (2 : ℝ) ^ (-3 * ρ ^ 2 * (n : ℝ) ^ 2 / 16 +
                5 * (n : ℝ) / 8 + 1 / 4) :=
        Finset.sum_le_sum fun w hw => Finset.sum_le_sum fun i _ => hentry w hw i
      _ = ∑ w ∈ Finset.Ico w₀ (n + 1),
          (∑ i, D w i (n - w) / A w i) *
            ((eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ n)) *
              (2 : ℝ) ^ (-3 * ρ ^ 2 * (n : ℝ) ^ 2 / 16 +
                5 * (n : ℝ) / 8 + 1 / 4)) := by
        apply Finset.sum_congr rfl
        intro w _
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        ring
      _ = (∑ w ∈ Finset.Ico w₀ (n + 1), ∑ i, D w i (n - w) / A w i) *
          ((eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ n)) *
            (2 : ℝ) ^ (-3 * ρ ^ 2 * (n : ℝ) ^ 2 / 16 +
              5 * (n : ℝ) / 8 + 1 / 4)) := by
        rw [← Finset.sum_mul]
      _ = _ := by ring
  have hsplit :
      (eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ n) *
        (∑ w ∈ Finset.Ico w₀ (n + 1), ∑ i, D w i (n - w) / A w i)) *
          (2 : ℝ) ^ (-3 * ρ ^ 2 * (n : ℝ) ^ 2 / 16 +
            5 * (n : ℝ) / 8 + 1 / 4) =
      (eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ n) *
        (2 : ℝ) ^ (5 * (n : ℝ) / 8 + 1 / 4) *
          (∑ w ∈ Finset.Ico w₀ (n + 1), ∑ i, D w i (n - w) / A w i)) *
        (2 : ℝ) ^ (-3 * ρ ^ 2 * (n : ℝ) ^ 2 / 16) := by
    rw [show -3 * ρ ^ 2 * (n : ℝ) ^ 2 / 16 + 5 * n / 8 + 1 / 4 =
      (5 * n / 8 + 1 / 4) + (-3 * ρ ^ 2 * n ^ 2 / 16) by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    ring
  calc
    _ ≤ (eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ n) *
        (∑ w ∈ Finset.Ico w₀ (n + 1), ∑ i, D w i (n - w) / A w i)) *
          (2 : ℝ) ^ (-3 * ρ ^ 2 * (n : ℝ) ^ 2 / 16 +
            5 * (n : ℝ) / 8 + 1 / 4) := hsum
    _ = _ := hsplit
    _ ≤ (2 : ℝ) ^ (ρ ^ 2 * (n : ℝ) ^ 2 / 16) *
        (2 : ℝ) ^ (-3 * ρ ^ 2 * (n : ℝ) ^ 2 / 16) :=
      mul_le_mul_of_nonneg_right hoverhead (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

end SymmetricSubgroupAsymptotics

end
