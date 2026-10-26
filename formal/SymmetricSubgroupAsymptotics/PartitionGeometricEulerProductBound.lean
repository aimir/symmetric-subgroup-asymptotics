import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! A finite Euler-product bound at the rational argument 5/7.
The first eight factors are checked exactly; the rest are bounded by
a finite geometric sum. No infinite product or partition enumeration
is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.PartitionGeometricEulerProductBound

theorem one_sub_sum_le_product (s : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ i∈s, 0≤f i ∧ f i≤1) :
    1-(∑ i∈s, f i)≤∏ i∈s, (1-f i) := by
  rw [Finset.prod_one_sub_ordered]
  apply sub_le_sub_left
  apply Finset.sum_le_sum
  intro i hi
  have hp : (∏ j∈s with j<i, (1-f j))≤1 := by
    apply Finset.prod_le_one
    · intro j hj
      exact sub_nonneg.mpr (hf j (Finset.mem_filter.mp hj).1).2
    · intro j hj
      exact sub_le_self _ (hf j (Finset.mem_filter.mp hj).1).1
  exact (mul_le_mul_of_nonneg_left hp (hf i hi).1).trans_eq (mul_one _)

def eulerProduct (n : ℕ) : ℝ :=
  ∏ j∈Finset.Ico 1 (n+1), (1-(5/7 : ℝ)^j)

theorem first_eight_lower : (1/32 : ℝ)≤eulerProduct 8 := by
  have hs : Finset.Ico 1 9=({1,2,3,4,5,6,7,8} : Finset ℕ) := by decide
  norm_num [eulerProduct,hs]

theorem product_lower_bound (n : ℕ) : (1/64 : ℝ)≤eulerProduct n := by
  have hpow (j : ℕ) : (5/7 : ℝ)^j≤1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  by_cases hn : n≤8
  · have hm : eulerProduct 8≤eulerProduct n := by
      unfold eulerProduct
      apply Finset.prod_le_prod_of_subset_of_le_one
      · intro j hj
        obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hj
        exact Finset.mem_Ico.mpr ⟨hlo,by omega⟩
      · intro j _
        exact sub_nonneg.mpr (hpow j)
      · intro j _ _
        exact sub_le_self _ (pow_nonneg (by norm_num) j)
    exact (by norm_num : (1/64 : ℝ)≤1/32).trans (first_eight_lower.trans hm)
  · have hsum : (∑ j∈Finset.Ico 9 (n+1), (5/7 : ℝ)^j)≤1/2 := by
      exact (geom_sum_Ico_le_of_lt_one (by norm_num : (0 : ℝ)≤5/7)
        (by norm_num : (5/7 : ℝ)<1)).trans (by norm_num)
    have htail : (1/2 : ℝ)≤∏ j∈Finset.Ico 9 (n+1), (1-(5/7 : ℝ)^j) := by
      have h := one_sub_sum_le_product (Finset.Ico 9 (n+1))
        (fun j => (5/7 : ℝ)^j) (fun j _ => ⟨pow_nonneg (by norm_num) j,hpow j⟩)
      linarith
    calc
      (1/64 : ℝ)=(1/32)*(1/2) := by norm_num
      _≤eulerProduct 8*(∏ j∈Finset.Ico 9 (n+1), (1-(5/7 : ℝ)^j)) :=
        mul_le_mul first_eight_lower htail (by norm_num)
          (by linarith [first_eight_lower])
      _=eulerProduct n := by
        exact Finset.prod_Ico_consecutive (fun j => (1-(5/7 : ℝ)^j))
          (by decide : 1≤9) (by omega)

theorem inverse_product_le_sixtyFour (n : ℕ) : (eulerProduct n)⁻¹≤64 := by
  have h := product_lower_bound n
  have hp : 0<eulerProduct n := (by norm_num : (0 : ℝ)<1/64).trans_le h
  have hi : (1 : ℝ)*(eulerProduct n)⁻¹≤64 :=
    (mul_inv_le_iff₀ hp).2 (by nlinarith)
  simpa only [one_mul] using hi

end SymmetricSubgroupAsymptotics.PartitionGeometricEulerProductBound
