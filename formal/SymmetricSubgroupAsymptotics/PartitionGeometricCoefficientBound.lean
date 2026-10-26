import SymmetricSubgroupAsymptotics.RestrictedPartitionCardinalityRecurrence
import SymmetricSubgroupAsymptotics.PartitionGeometricEulerProductBound
import Mathlib.Tactic.Ring

/-! A finite coefficient bound from the literal restricted-partition recurrence.
The finite weighted sum is charged against the finite Euler product; no
infinite-product identity or partition enumeration is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.PartitionGeometricCoefficientBound
open RestrictedPartitionCardinalityRecurrence
open PartitionGeometricEulerProductBound

theorem count_recurrence (n k : ℕ) :
    count n (k+1)=count n k+
      (if k+1≤n then count (n-(k+1)) (k+1) else 0) := by
  simpa only [card_eq_count] using card_recurrence n k

def weightedSum (N k : ℕ) (r : ℝ) : ℝ :=
  ∑ n∈Finset.range (N+1), (count n k : ℝ)*r^n

theorem weightedSum_nonneg (N k : ℕ) (r : ℝ) (hr : 0≤r) :
    0≤weightedSum N k r := by
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr _)

private theorem shifted_sum_le (N d : ℕ) (f : ℕ → ℝ) (hf : ∀ n,0≤f n) :
    (∑ n∈Finset.range (N+1), if d≤n then f (n-d) else 0)≤
      ∑ n∈Finset.range (N+1),f n := by
  let s := (Finset.range (N+1)).filter (fun n => d≤n)
  have hinj : Set.InjOn (fun n => n-d) s := by
    intro i hi j hj he
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    change i-d=j-d at he
    omega
  have hsub : s.image (fun n => n-d)⊆Finset.range (N+1) := by
    intro i hi
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hi
    have hn' := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
    exact Finset.mem_range.mpr (by omega)
  calc
    _=∑ n∈s,f (n-d) := by simp only [s,Finset.sum_filter]
    _=∑ n∈s.image (fun n => n-d),f n := (Finset.sum_image hinj).symm
    _≤_ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf n)

theorem weightedSum_step (N k : ℕ) (r : ℝ) (hr : 0≤r) :
    (1-r^(k+1))*weightedSum N (k+1) r≤weightedSum N k r := by
  have he : weightedSum N (k+1) r=weightedSum N k r+
      r^(k+1)*(∑ n∈Finset.range (N+1),
        if k+1≤n then (count (n-(k+1)) (k+1) : ℝ)*r^(n-(k+1)) else 0) := by
    unfold weightedSum
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [count_recurrence]
    by_cases h : k+1≤n
    · rw [if_pos h,if_pos h,Nat.cast_add]
      have hp : r^n=r^(k+1)*r^(n-(k+1)) := by
        rw [←pow_add,Nat.add_sub_of_le h]
      rw [hp]
      ring
    · simp only [if_neg h,mul_zero,add_zero]
  have hh := shifted_sum_le N (k+1)
    (fun n => (count n (k+1) : ℝ)*r^n)
    (fun n => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr _))
  have hm := mul_le_mul_of_nonneg_left hh (pow_nonneg hr (k+1))
  change _≤r^(k+1)*weightedSum N (k+1) r at hm
  nlinarith [he]

theorem weightedSum_zero (N : ℕ) (r : ℝ) : weightedSum N 0 r=1 := by
  have hc (n : ℕ) : count n 0=if n=0 then 1 else 0 := by
    cases n <;> simp [count]
  simp [weightedSum,hc]

theorem weightedSum_mul_product_le_one (N k : ℕ) :
    weightedSum N k (5/7)*eulerProduct k≤1 := by
  induction k with
  | zero => simp [weightedSum_zero,eulerProduct]
  | succ k ih =>
    have hs := weightedSum_step N k (5/7) (by norm_num)
    have hp : 0≤eulerProduct k := (by norm_num : (0 : ℝ)≤1/64).trans
      (product_lower_bound k)
    have hm := mul_le_mul_of_nonneg_right hs hp
    have he : eulerProduct (k+1)=eulerProduct k*(1-(5/7 : ℝ)^(k+1)) := by
      unfold eulerProduct
      rw [Finset.prod_Ico_succ_top (by omega)]
    rw [he]
    nlinarith [ih,hm]

theorem weighted_coefficient_le_sixtyFour (n : ℕ) :
    (Nat.card (Nat.Partition n) : ℝ)*(5/7 : ℝ)^n≤64 := by
  have hs : (count n n : ℝ)*(5/7 : ℝ)^n≤weightedSum n n (5/7) := by
    unfold weightedSum
    apply Finset.single_le_sum (f := fun j => (count j n : ℝ)*(5/7 : ℝ)^j)
      (a := n)
    · intro j _
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)
    · exact Finset.mem_range.mpr (by omega)
  have hp := product_lower_bound n
  have hz := weightedSum_nonneg n n (5/7) (by norm_num)
  have hm := weightedSum_mul_product_le_one n n
  rw [partition_card_eq_count]
  nlinarith [mul_le_mul_of_nonneg_left hp hz]

theorem partition_card_mul_five_pow_le (n : ℕ) :
    Nat.card (Nat.Partition n)*5^n≤64*7^n := by
  have h := weighted_coefficient_le_sixtyFour n
  rw [div_pow] at h
  have hp : (0 : ℝ)<7^n := pow_pos (by norm_num) _
  have hr : (Nat.card (Nat.Partition n) : ℝ)*5^n≤64*7^n := by
    apply (div_le_iff₀ hp).mp
    simpa only [mul_div_assoc] using h
  exact_mod_cast hr

end SymmetricSubgroupAsymptotics.PartitionGeometricCoefficientBound
