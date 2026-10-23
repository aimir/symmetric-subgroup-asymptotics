import SymmetricSubgroupAsymptotics.PartitionNoOneShrink
import Mathlib.Logic.Equiv.Sum
import Mathlib.Data.Nat.Fib.Basic

/-! A partition containing one loses that one injectively. A partition
without one loses two by the checked two-smallest shrink. These two
actual injections give the Fibonacci recurrence bound, with the empty
partition retained at degree zero. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PartitionFibonacciBound
open PartitionNoOneShrink

abbrev HasOne (n : ℕ) := {p : Nat.Partition n // 1 ∈ p.parts}

def eraseOne {n : ℕ} (p : HasOne n) : Nat.Partition (n-1) where
  parts := p.val.parts.erase 1
  parts_pos ha := p.val.parts_pos (Multiset.mem_of_mem_erase ha)
  parts_sum := by
    have h := congrArg Multiset.sum (Multiset.cons_erase p.property)
    rw [Multiset.sum_cons, p.val.parts_sum] at h
    omega

theorem eraseOne_injective (n : ℕ) : Function.Injective (@eraseOne n) := by
  intro p q he
  have h := congrArg Nat.Partition.parts he
  apply Subtype.ext
  apply Nat.Partition.ext
  calc
    p.val.parts = 1 ::ₘ p.val.parts.erase 1 := (Multiset.cons_erase p.property).symm
    _ = 1 ::ₘ q.val.parts.erase 1 := congrArg (fun s : Multiset ℕ => 1 ::ₘ s) h
    _ = q.val.parts := Multiset.cons_erase q.property

theorem partition_card_recurrence (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (Nat.Partition n) ≤
      Nat.card (Nat.Partition (n-1)) + Nat.card (Nat.Partition (n-2)) := by
  have he : Nat.card (Nat.Partition n) = Nat.card (HasOne n) + Nat.card (NoOnes n) := by
    rw [← Nat.card_sum]
    exact (Nat.card_congr (Equiv.sumCompl (fun p : Nat.Partition n => 1 ∈ p.parts))).symm
  rw [he]
  exact Nat.add_le_add
    (Nat.card_le_card_of_injective _ (eraseOne_injective n)) (noOnes_card_le hn)

theorem partition_card_le_fib (n : ℕ) :
    Nat.card (Nat.Partition n) ≤ Nat.fib (n+1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n=0
    · subst n
      simp only [Nat.card_unique, Nat.zero_add, Nat.fib_one, le_refl]
    by_cases hn1 : n=1
    · subst n
      simpa only [Nat.card_unique, Nat.fib_two] using (le_refl (1:ℕ))
    have hn : 2 ≤ n := by omega
    have hprev := ih (n-1) (by omega)
    have hprev2 := ih (n-2) (by omega)
    have hsum : Nat.fib ((n-1)+1) + Nat.fib ((n-2)+1) = Nat.fib (n+1) := by
      have h1 : (n-1)+1=n := by omega
      have h2 : (n-2)+1=n-1 := by omega
      rw [h1,h2,Nat.fib_add_one (by omega : n ≠ 0),Nat.add_comm]
    exact (partition_card_recurrence n hn).trans
      ((Nat.add_le_add hprev hprev2).trans_eq hsum)

end SymmetricSubgroupAsymptotics.PartitionFibonacciBound
