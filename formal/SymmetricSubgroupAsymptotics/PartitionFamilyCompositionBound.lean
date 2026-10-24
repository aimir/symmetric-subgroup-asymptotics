import SymmetricSubgroupAsymptotics.BinaryPartitionBudget

/-! Products of partition choices are bounded by composition counts.
Every multiplicity is positive on the actual support, so a nonempty
family retains one power-of-two saving. No partition-number table or
false general partition supermultiplicativity is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.PartitionFamilyCompositionBound

theorem partition_card_le_composition_power (n : ℕ) :
    Nat.card (Nat.Partition n) ≤ 2^(n-1) := by
  have h := Nat.card_le_card_of_surjective (Nat.Partition.ofComposition n)
    Nat.Partition.ofComposition_surj
  have hc : Nat.card (Composition n) = 2^(n-1) := by
    rw [Nat.card_eq_fintype_card,composition_card]
  exact hc ▸ h

theorem partition_family_card_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (m : ι → ℕ) (hm : ∀ i, 0 < m i) :
    Nat.card ((i : ι) → Nat.Partition (m i)) ≤ 2^((∑ i : ι, m i)-1) := by
  have he : (∑ i : ι, (m i-1)) + Fintype.card ι = ∑ i : ι, m i := by
    calc
      _ = ∑ i : ι, ((m i-1)+1) := by
        simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
          nsmul_eq_mul,mul_one,Nat.cast_id]
      _ = _ := Finset.sum_congr rfl (fun i _ =>
        Nat.sub_add_cancel (Nat.succ_le_of_lt (hm i)))
  have hc : 0 < Fintype.card ι := Fintype.card_pos
  have hx : (∑ i : ι, (m i-1)) ≤ (∑ i : ι, m i)-1 := by omega
  calc
    _ = ∏ i : ι, Nat.card (Nat.Partition (m i)) := Nat.card_pi
    _ ≤ ∏ i : ι, 2^(m i-1) :=
      Finset.prod_le_prod' (fun i _ => partition_card_le_composition_power (m i))
    _ = 2^(∑ i : ι, (m i-1)) :=
      Finset.prod_pow_eq_pow_sum Finset.univ (fun i => m i-1) 2
    _ ≤ _ := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hx

theorem partition_family_card_le_of_sum_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (m : ι → ℕ) (hm : ∀ i, 0 < m i) (n : ℕ) (hn : (∑ i : ι, m i) ≤ n) :
    Nat.card ((i : ι) → Nat.Partition (m i)) ≤ 2^(n-1) :=
  (partition_family_card_le m hm).trans
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.sub_le_sub_right hn 1))

end SymmetricSubgroupAsymptotics.PartitionFamilyCompositionBound
