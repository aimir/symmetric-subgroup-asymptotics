import SymmetricSubgroupAsymptotics.PrimeGridSymmetricChains
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

/-! Actual Boolean coset grids have the exact binomial rank distribution.
The weighted identity is used in replacing uniform chains by Boolean ones. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics

/-- This counts the original recursive grid points, rather than a
formal polynomial introduced as a new rank distribution. -/
theorem binaryGrid_rank_sum (n t : ℕ) :
    (∑ x : PrimeCosetGrid 2 n, if primeGridRank 2 n x=t then 1 else 0)=n.choose t := by
  induction n generalizing t with
  | zero =>
    cases t <;> simp [PrimeCosetGrid,primeGridRank]
  | succ n ih =>
    change (∑ x : Fin 2×PrimeCosetGrid 2 n,
      if x.1.val+primeGridRank 2 n x.2=t then 1 else 0)=(n+1).choose t
    rw [Fintype.sum_prod_type,Fin.sum_univ_two]
    simp only [Fin.val_zero,Fin.val_one,zero_add]
    cases t with
    | zero =>
      simp only [Nat.add_eq_zero_iff,Nat.one_ne_zero,false_and,if_false,
        Finset.sum_const_zero,Nat.add_zero,Nat.choose_zero_right]
      simpa only [Nat.choose_zero_right] using ih 0
    | succ t =>
      have he (x : PrimeCosetGrid 2 n) :
          (1+primeGridRank 2 n x=t+1) ↔ (primeGridRank 2 n x=t) := by omega
      simp only [he,ih,Nat.choose_succ_succ']
      exact Nat.add_comm _ _

/-- An arbitrary test of the actual Boolean rank is the corresponding
binomially weighted finite sum. -/
theorem binaryGrid_weighted_sum (n : ℕ) (f : ℕ → ℕ) :
    (∑ x : PrimeCosetGrid 2 n, f (primeGridRank 2 n x))=
      ∑ i : Fin (n+1),n.choose i.val*f i.val := by
  let r : PrimeCosetGrid 2 n → Fin (n+1) := fun x =>
    ⟨primeGridRank 2 n x,by
      have hb := (primeGridSymmetricChains 2 n (by decide)).rank_bounds x
      simp only [Nat.reduceSub,mul_one] at hb
      omega⟩
  have hsum := Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (g := r)
    (fun x _ => Finset.mem_univ (r x)) (fun x => f (primeGridRank 2 n x))
  rw [←hsum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ x∈Finset.univ.filter (fun x => r x=i),f (primeGridRank 2 n x))=
        (∑ x : PrimeCosetGrid 2 n,if primeGridRank 2 n x=i.val then 1 else 0)*f i.val := by
      rw [Finset.sum_filter,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : r x=i
      · have hv := congrArg Fin.val hx
        change primeGridRank 2 n x=i.val at hv
        simp only [hx,if_true,hv,one_mul]
      · have hv : primeGridRank 2 n x≠i.val := by
          intro hv
          apply hx
          exact Fin.ext hv
        simp only [hx,hv,if_false,zero_mul]
    _ = n.choose i.val*f i.val := by rw [binaryGrid_rank_sum]

end SymmetricSubgroupAsymptotics
