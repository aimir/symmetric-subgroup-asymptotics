import SymmetricSubgroupAsymptotics.PartitionFibonacciBound

/-! The actual partition cardinalities are monotone by adjoining a part
of size one. Together with the checked two-step partition injection this
gives a three-step growth factor of five, independently of any table. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.PartitionThreeStepRecurrence

def addOne (n : ℕ) (p : Nat.Partition n) : Nat.Partition (n+1) where
  parts := 1 ::ₘ p.parts
  parts_pos := by
    intro i hi
    rcases Multiset.mem_cons.mp hi with rfl | hi
    · exact Nat.zero_lt_one
    · exact p.parts_pos hi
  parts_sum := by rw [Multiset.sum_cons, p.parts_sum, Nat.add_comm]

theorem addOne_injective (n : ℕ) : Function.Injective (addOne n) := by
  intro p q he
  apply Nat.Partition.ext
  exact (Multiset.cons_inj_right 1).mp (congrArg Nat.Partition.parts he)

theorem card_le_succ (n : ℕ) :
    Nat.card (Nat.Partition n) ≤ Nat.card (Nat.Partition (n+1)) :=
  Nat.card_le_card_of_injective (addOne n) (addOne_injective n)

theorem card_three_step_le (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (Nat.Partition (n+3)) ≤ 5 * Nat.card (Nat.Partition n) := by
  have hprev : Nat.card (Nat.Partition (n-1)) ≤ Nat.card (Nat.Partition n) := by
    simpa only [show (n-1)+1=n by omega] using card_le_succ (n-1)
  have h1 : Nat.card (Nat.Partition (n+1)) ≤
      Nat.card (Nat.Partition n) + Nat.card (Nat.Partition (n-1)) := by
    simpa only [show n+1-1=n by omega, show n+1-2=n-1 by omega] using
      PartitionFibonacciBound.partition_card_recurrence (n+1) (by omega)
  have h2 : Nat.card (Nat.Partition (n+2)) ≤
      Nat.card (Nat.Partition (n+1)) + Nat.card (Nat.Partition n) := by
    simpa only [show n+2-1=n+1 by omega, show n+2-2=n by omega] using
      PartitionFibonacciBound.partition_card_recurrence (n+2) (by omega)
  have h3 : Nat.card (Nat.Partition (n+3)) ≤
      Nat.card (Nat.Partition (n+2)) + Nat.card (Nat.Partition (n+1)) := by
    simpa only [show n+3-1=n+2 by omega, show n+3-2=n+1 by omega] using
      PartitionFibonacciBound.partition_card_recurrence (n+3) (by omega)
  omega

end SymmetricSubgroupAsymptotics.PartitionThreeStepRecurrence
