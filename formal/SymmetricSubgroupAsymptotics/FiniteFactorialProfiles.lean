import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Finite profile sums with their original denominators

Every coordinate retains its own denominator and multiplicity factorial.
Enlarging a finite family of profiles to a finite coordinate box gives an
exponential bound. No assertion about which physical profiles occur is made.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.FiniteFactorialProfiles

variable {ι : Type*} [Fintype ι]

/-- The original product weight, written in exponential-series form. -/
def weight (w : ι → ℝ) (m : ι → ℕ) : ℝ :=
  ∏ i, (w i)⁻¹ ^ m i / ((m i).factorial : ℝ)

theorem weight_eq_reciprocal_denominator (w : ι → ℝ) (m : ι → ℕ) :
    weight w m = 1 / (∏ i, w i ^ m i * ((m i).factorial : ℝ)) := by
  classical
  unfold weight
  rw [one_div, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [mul_inv_rev, inv_pow, div_eq_mul_inv]
  exact mul_comm _ _

theorem weight_nonneg (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (m : ι → ℕ) :
    0 ≤ weight w m := by
  apply Finset.prod_nonneg
  intro i _
  exact div_nonneg (pow_nonneg (inv_nonneg.mpr (hw i)) _)
    (Nat.cast_nonneg _)

/-- A finite coordinate box is bounded by the product of the complete
exponential series. The bounds may differ between original colours. -/
theorem sum_le_exp_of_bounded (S : Finset (ι → ℕ)) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (bound : ι → ℕ)
    (hbound : ∀ m ∈ S, ∀ i, m i ≤ bound i) :
    ∑ m ∈ S, weight w m ≤ Real.exp (∑ i, (w i)⁻¹) := by
  classical
  have hsub : S ⊆ Fintype.piFinset (fun i => Finset.range (bound i + 1)) := by
    intro m hm
    exact Fintype.mem_piFinset.mpr fun i =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound m hm i))
  calc
    ∑ m ∈ S, weight w m ≤
        ∑ m ∈ Fintype.piFinset (fun i => Finset.range (bound i + 1)), weight w m :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun m _ _ => weight_nonneg w (fun i => (hw i).le) m)
    _ = ∏ i, ∑ k ∈ Finset.range (bound i + 1),
        (w i)⁻¹ ^ k / (k.factorial : ℝ) := by
      unfold weight
      exact (Finset.prod_univ_sum (fun i => Finset.range (bound i + 1))
        (fun i k => (w i)⁻¹ ^ k / (k.factorial : ℝ))).symm
    _ ≤ ∏ i, Real.exp ((w i)⁻¹) := by
      apply Finset.prod_le_prod
      · intro i _
        apply Finset.sum_nonneg
        intro k _
        exact div_nonneg (pow_nonneg (inv_nonneg.mpr (hw i).le) _)
          (Nat.cast_nonneg _)
      · intro i _
        exact Real.sum_le_exp_of_nonneg (inv_nonneg.mpr (hw i).le) _
    _ = Real.exp (∑ i, (w i)⁻¹) := (Real.exp_sum _ _).symm

/-- Every specified finite family admits the same bound; its coordinate
bounds are finite suprema, not extra mathematical hypotheses. -/
theorem sum_le_exp (S : Finset (ι → ℕ)) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) :
    ∑ m ∈ S, weight w m ≤ Real.exp (∑ i, (w i)⁻¹) := by
  classical
  apply sum_le_exp_of_bounded S w hw (fun i => S.sup (fun m => m i))
  intro m hm i
  exact Finset.le_sup (f := fun m => m i) hm

/-- In particular, no exact normalizer orders are needed: denominators
at least one give a constant depending only on the number of colours. -/
theorem sum_le_exp_card (S : Finset (ι → ℕ)) (w : ι → ℝ)
    (hw : ∀ i, 1 ≤ w i) :
    ∑ m ∈ S, weight w m ≤ Real.exp (Fintype.card ι : ℝ) := by
  have hsum : (∑ i, (w i)⁻¹) ≤ (Fintype.card ι : ℝ) := by
    calc
      ∑ i, (w i)⁻¹ ≤ ∑ _i : ι, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [one_div, inv_one] using
          one_div_le_one_div_of_le (show (0 : ℝ) < 1 from zero_lt_one) (hw i)
      _ = _ := by simp
  exact (sum_le_exp S w (fun i => lt_of_lt_of_le zero_lt_one (hw i))).trans
    (Real.exp_le_exp.mpr hsum)

/-- Insert a common proved model bound without replacing the original
weights or merging distinct profiles. -/
theorem sum_mul_le_exp_card (S : Finset (ι → ℕ)) (w : ι → ℝ)
    (hw : ∀ i, 1 ≤ w i) (a : (ι → ℕ) → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ m ∈ S, a m ≤ C) :
    ∑ m ∈ S, weight w m * a m ≤ Real.exp (Fintype.card ι : ℝ) * C := by
  calc
    ∑ m ∈ S, weight w m * a m ≤ ∑ m ∈ S, weight w m * C := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_left (ha m hm)
        (weight_nonneg w (fun i => (zero_le_one.trans (hw i))) m)
    _ = (∑ m ∈ S, weight w m) * C := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (sum_le_exp_card S w hw) hC

end SymmetricSubgroupAsymptotics.FiniteFactorialProfiles
