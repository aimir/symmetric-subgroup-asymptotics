import SymmetricSubgroupAsymptotics.GrowingComparatorPadding

/-!
# Cold aggregation for a growing comparator menu

The group-theoretic certificate package will supply a direct bound on the
sum of its original weights.  This file converts that bound into the sharp
per-width cold coefficient used by the parametric transfer theorem.  The
entry type may vary with the removed width, and every original divisor is
kept inside the weighted sum.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- The cold contribution of all retained certificates at one actual width.
The certificate factor `D` may depend on the complement degree. -/
def growingQuotientColdWidthSum {ι : Type*} [Fintype ι]
    (b w : ℕ) (D : ι → ℕ → ℝ) (A α : ι → ℝ) : ℝ :=
  ∑ i, fusionWidthColdKernel b w (D i b) (A i) (α i)

theorem growingQuotientColdWidthSum_nonneg {ι : Type*} [Fintype ι]
    (b w : ℕ) (D : ι → ℕ → ℝ) (A α : ι → ℝ)
    (hD : ∀ i b, 0 ≤ D i b) (hA : ∀ i, 0 < A i) :
    0 ≤ growingQuotientColdWidthSum b w D A α := by
  unfold growingQuotientColdWidthSum
  exact Finset.sum_nonneg fun i _ =>
    fusionWidthColdKernel_nonneg b w (hD i b) (hA i)

/-- One original weighted menu bound implies the desired cold coefficient at
that width.  The displayed overhead is precisely the universal pointing
polynomial times `Σ D/A`; it is the interface later discharged by the
subquadratic certificate-mass theorem. -/
theorem growingQuotientColdWidthSum_le
    {ι : Type*} [Fintype ι]
    {ρ : ℝ} (n w : ℕ) (D : ι → ℕ → ℝ) (A α : ι → ℝ)
    (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8)
    (hw : 3 ≤ w) (hwn : w ≤ n)
    (hD : ∀ i b, 0 ≤ D i b) (hA : ∀ i, 0 < A i)
    (hgap : ∀ i,
      α i ≤ (halfDegree w : ℝ) / 4 - ρ * w / 4)
    (hoverhead :
      eulerProduct⁻¹ ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (w + 2)) *
          (2 : ℝ) ^ ((halfDegree w : ℝ) / 4 + 1 / 4) *
          (∑ i, D i (n - w) / A i) ≤
        (2 : ℝ) ^ (ρ * w * n / 16)) :
    growingQuotientColdWidthSum (n - w) w D A α ≤
      (2 : ℝ) ^ (-ρ * w * n / 8) := by
  let r := halfDegree w
  let b := n - w
  have hbcast : (b : ℝ) = (n : ℝ) - w := by
    dsimp [b]
    rw [Nat.cast_sub hwn]
  have hentry (i : ι) :
      fusionWidthColdKernel b w (D i b) (A i) (α i) ≤
        (eulerProduct⁻¹ ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (w + 2)) *
          (D i b / A i)) *
            (2 : ℝ) ^ (-ρ * w * b / 4 - (r : ℝ) ^ 2 / 4 +
              (r : ℝ) / 4 + 1 / 4) := by
    have hkernel := fusionWidthColdKernel_quadratic_le b w
      (hD i b) (hA i) (α := α i)
    have hn : b + w = n := Nat.sub_add_cancel hwn
    have hexp :
        -(r : ℝ) * b / 4 - (r : ℝ) ^ 2 / 4 + (r : ℝ) / 4 + 1 / 4 +
            α i * b ≤
          -ρ * w * b / 4 - (r : ℝ) ^ 2 / 4 + (r : ℝ) / 4 + 1 / 4 := by
      have hgapb := mul_le_mul_of_nonneg_right (hgap i)
        (show (0 : ℝ) ≤ b by positivity)
      dsimp [r]
      nlinarith
    rw [hn] at hkernel
    exact hkernel.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
      (mul_nonneg
        (mul_nonneg (pow_nonneg (inv_nonneg.mpr euler_positive.le) 2)
          (by positivity)) (div_nonneg (hD i b) (hA i).le)))
  have hsum : growingQuotientColdWidthSum b w D A α ≤
      (eulerProduct⁻¹ ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (w + 2)) *
        (∑ i, D i b / A i)) *
          (2 : ℝ) ^ (-ρ * w * b / 4 - (r : ℝ) ^ 2 / 4 +
            (r : ℝ) / 4 + 1 / 4) := by
    unfold growingQuotientColdWidthSum
    calc
      _ ≤ ∑ i, (eulerProduct⁻¹ ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (w + 2)) *
          (D i b / A i)) *
            (2 : ℝ) ^ (-ρ * w * b / 4 - (r : ℝ) ^ 2 / 4 +
              (r : ℝ) / 4 + 1 / 4) :=
        Finset.sum_le_sum fun i _ => hentry i
      _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hsplit :
      (eulerProduct⁻¹ ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (w + 2)) *
        (∑ i, D i b / A i)) *
          (2 : ℝ) ^ (-ρ * w * b / 4 - (r : ℝ) ^ 2 / 4 +
            (r : ℝ) / 4 + 1 / 4) =
      (eulerProduct⁻¹ ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (w + 2)) *
        (2 : ℝ) ^ ((r : ℝ) / 4 + 1 / 4) *
          (∑ i, D i b / A i)) *
        (2 : ℝ) ^ (-ρ * w * b / 4 - (r : ℝ) ^ 2 / 4) := by
    rw [show -ρ * (w : ℝ) * b / 4 - (r : ℝ) ^ 2 / 4 + r / 4 + 1 / 4 =
      (r / 4 + 1 / 4) + (-ρ * w * b / 4 - r ^ 2 / 4) by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    ring
  have hoverhead' :
      eulerProduct⁻¹ ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (w + 2)) *
          (2 : ℝ) ^ ((r : ℝ) / 4 + 1 / 4) *
          (∑ i, D i b / A i) ≤
        (2 : ℝ) ^ (ρ * w * n / 16) := by
    simpa only [r, b] using hoverhead
  have hmain : growingQuotientColdWidthSum b w D A α ≤
      (2 : ℝ) ^ (ρ * w * n / 16) *
        (2 : ℝ) ^ (-ρ * w * b / 4 - (r : ℝ) ^ 2 / 4) := by
    apply hsum.trans
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right hoverhead' (by positivity)
  have hwr : w ≤ 3 * r := by
    dsimp [r, halfDegree]
    omega
  have hwrR : (w : ℝ) ≤ 3 * r := by exact_mod_cast hwr
  have hsq : 3 * (w : ℝ) ^ 2 ≤ 32 * (r : ℝ) ^ 2 := by
    have hw0 : (0 : ℝ) ≤ w := by positivity
    have hr0 : (0 : ℝ) ≤ r := by positivity
    nlinarith [sq_nonneg (3 * (r : ℝ) - w)]
  have hρ0 : 0 ≤ ρ := hρ.le
  have hnterm : 0 ≤ ρ * w * ((n : ℝ) - w) :=
    mul_nonneg (mul_nonneg hρ0 (by positivity))
      (sub_nonneg.mpr (by exact_mod_cast hwn))
  have hexp :
      ρ * w * n / 16 + (-ρ * w * b / 4 - (r : ℝ) ^ 2 / 4) ≤
        -ρ * w * n / 8 := by
    rw [hbcast]
    nlinarith
  calc
    _ ≤ (2 : ℝ) ^ (ρ * w * n / 16) *
        (2 : ℝ) ^ (-ρ * w * b / 4 - (r : ℝ) ^ 2 / 4) := hmain
    _ = (2 : ℝ) ^
        (ρ * w * n / 16 + (-ρ * w * b / 4 - (r : ℝ) ^ 2 / 4)) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

end SymmetricSubgroupAsymptotics

end
