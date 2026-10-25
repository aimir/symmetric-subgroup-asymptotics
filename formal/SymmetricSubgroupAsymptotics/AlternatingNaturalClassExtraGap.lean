import SymmetricSubgroupAsymptotics.AlternatingSmallPartitionCompositionCapacity
import SymmetricSubgroupAsymptotics.PartitionThreeStepRecurrence
import SymmetricSubgroupAsymptotics.AlternatingSixClassBound
import Mathlib.Tactic.Ring

/-! The actual alternating class count pays one extra GM exponent in
every natural degree at least five. Small partition capacities seed a
single three-step induction for the whole family. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AlternatingNaturalClassExtraGap
open FinitePartitionCompositionMenu AlternatingSmallPartitionCompositionCapacity

private theorem partition_seven : Nat.card (Nat.Partition 7) ≤ 15 := by
  have hh := partition_card_le_menu_card 7
  rwa [menu_seven_card] at hh

private theorem partition_eight : Nat.card (Nat.Partition 8) ≤ 22 := by
  have hh := partition_card_le_menu_card 8
  rwa [menu_eight_card] at hh

private theorem partition_nine : Nat.card (Nat.Partition 9) ≤ 37 := by
  have hh := PartitionFibonacciBound.partition_card_recurrence 9 (by decide)
  norm_num only [Nat.reduceSub] at hh
  have h7 := partition_seven
  have h8 := partition_eight
  omega

private theorem partition_ten : Nat.card (Nat.Partition 10) ≤ 59 := by
  have hh := PartitionFibonacciBound.partition_card_recurrence 10 (by decide)
  norm_num only [Nat.reduceSub] at hh
  have h8 := partition_eight
  have h9 := partition_nine
  omega

theorem partition_cube_le (m : ℕ) (hm : 8 ≤ m) :
    Nat.card (Nat.Partition m)^3 ≤ 5^(m-2) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases h8 : m = 8
    · subst m
      exact (Nat.pow_le_pow_left partition_eight 3).trans (by norm_num)
    by_cases h9 : m = 9
    · subst m
      exact (Nat.pow_le_pow_left partition_nine 3).trans (by norm_num)
    by_cases h10 : m = 10
    · subst m
      exact (Nat.pow_le_pow_left partition_ten 3).trans (by norm_num)
    have hprev := ih (m-3) (by omega) (by omega : 8 ≤ m-3)
    have hstep := PartitionThreeStepRecurrence.card_three_step_le (m-3) (by omega)
    rw [show (m-3)+3=m by omega] at hstep
    calc
      Nat.card (Nat.Partition m)^3 ≤ (5*Nat.card (Nat.Partition (m-3)))^3 :=
        Nat.pow_le_pow_left hstep 3
      _ = 5^3*Nat.card (Nat.Partition (m-3))^3 := mul_pow _ _ _
      _ ≤ 5^3*5^((m-3)-2) := Nat.mul_le_mul_left _ hprev
      _ = 5^(m-2) := by rw [← pow_add]; congr 1; omega

theorem alternating_class_cube_le (m : ℕ) (hm : 5 ≤ m) :
    Nat.card (ConjClasses (alternatingGroup (Fin m)))^3 ≤ 5^(m-2) := by
  by_cases h5 : m = 5
  · subst m
    exact (Nat.pow_le_pow_left alternating_five_class_card_le 3).trans (by norm_num)
  by_cases h6 : m = 6
  · subst m
    exact (Nat.pow_le_pow_left
      AlternatingSixClassBound.alternating_six_class_card_le_seven 3).trans (by norm_num)
  by_cases h7 : m = 7
  · subst m
    exact (Nat.pow_le_pow_left alternating_seven_class_card_le 3).trans (by norm_num)
  have hpart : Nat.card (ConjClasses (alternatingGroup (Fin m))) ≤
      Nat.card (Nat.Partition m) := by
    simpa only [Fintype.card_fin] using
      (AlternatingConjugacyPartitionBound.class_card_le_partitions
        (I := Fin m) (by simpa only [Fintype.card_fin] using (show 2 ≤ m by omega)))
  exact (Nat.pow_le_pow_left hpart 3).trans (partition_cube_le m (by omega))

end SymmetricSubgroupAsymptotics.AlternatingNaturalClassExtraGap
