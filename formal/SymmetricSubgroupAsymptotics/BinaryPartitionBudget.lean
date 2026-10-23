import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! A uniform coarse budget for binary colored partitions. Every
partition is an image of a composition, so no partition-number census
is required. The resulting budget meets the GM cube from n=7 onward. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryPartitionBudget

abbrev PairedPartitions (n : ℕ) :=
  Σi : Fin (n+1),Nat.Partition i.val × Nat.Partition (n-i.val)

theorem partition_card_le_power (n : ℕ) : Nat.card (Nat.Partition n)≤2^n := by
  have h := Nat.card_le_card_of_surjective (Nat.Partition.ofComposition n)
    Nat.Partition.ofComposition_surj
  have hc : Nat.card (Composition n)=2^(n-1) := by
    rw [Nat.card_eq_fintype_card,composition_card]
  rw [hc] at h
  exact h.trans (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.sub_le n 1))

theorem pairedPartitions_card_le (n : ℕ) :
    Nat.card (PairedPartitions n)≤(n+1)*2^n := by
  rw [Nat.card_sigma]
  calc
    (∑i : Fin (n+1),Nat.card (Nat.Partition i.val × Nat.Partition (n-i.val)))=
        ∑i : Fin (n+1),Nat.card (Nat.Partition i.val)*Nat.card (Nat.Partition (n-i.val)) := by
      simp only [Nat.card_prod]
    _≤∑i : Fin (n+1),2^i.val*2^(n-i.val) :=
      Finset.sum_le_sum (fun i _ => Nat.mul_le_mul
        (partition_card_le_power i.val) (partition_card_le_power (n-i.val)))
    _=∑_i : Fin (n+1),2^n := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← pow_add,Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]
    _=(n+1)*2^n := by simp

theorem coarse_cube_le_garonziMaroti (n : ℕ) (hn : 7≤n) :
    ((n+1)*2^n)^3≤5^(2*n-1) := by
  induction n,hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hs : 8*(n+2)^3≤25*(n+1)^3 := by nlinarith [Nat.zero_le (n^3)]
    calc
      ((n+1+1)*2^(n+1))^3=8*(n+2)^3*(2^n)^3 := by rw [pow_succ]; ring
      _≤25*(n+1)^3*(2^n)^3 := Nat.mul_le_mul_right _ hs
      _=25*(((n+1)*2^n)^3) := by ring
      _≤25*5^(2*n-1) := Nat.mul_le_mul_left 25 ih
      _=5^(2*(n+1)-1) := by
        have he : 2*(n+1)-1=(2*n-1)+2 := by omega
        rw [he,pow_add]
        norm_num [Nat.mul_comm]

theorem pairedPartitions_cube_le (n : ℕ) (hn : 7≤n) :
    Nat.card (PairedPartitions n)^3≤5^(2*n-1) :=
  (Nat.pow_le_pow_left (pairedPartitions_card_le n) 3).trans
    (coarse_cube_le_garonziMaroti n hn)

end SymmetricSubgroupAsymptotics.BinaryPartitionBudget
