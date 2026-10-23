import SymmetricSubgroupAsymptotics.AlternatingSixPartitionCapacity
import SymmetricSubgroupAsymptotics.AlternatingConjugacyPartitionBound

/-! The selected weighted-count certificate bounds ACTUAL full cycle
partitions in degree six. The checked alternating conjugacy-fibre theorem
then gives seven classes, without assuming a class table. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.AlternatingSixClassBound
open AlternatingSixPartitionCapacity AlternatingConjugacyPartitionBound
open DistinctOddPartitionInjection

private theorem decoded_count (p : Nat.Partition 6) (i : ℕ) (hi : 0 < i) :
    p.toFinsuppAntidiag i / i = p.parts.count i := by
  change p.parts.count i * i / i = p.parts.count i
  exact Nat.mul_div_cancel _ hi

private theorem decoded_card (p : Nat.Partition 6) :
    decodedCard p.toFinsuppAntidiag = p.parts.card := by
  unfold decodedCard
  calc
    _ = ∑ i ∈ Finset.Icc 1 6, p.parts.count i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact decoded_count p i (Finset.mem_Icc.mp hi).1
    _ = _ := Multiset.sum_count_eq_card (fun i hi =>
      Finset.mem_Icc.mpr ⟨p.parts_pos hi, Nat.Partition.le_of_mem_parts hi⟩)

private theorem weighted_mem (p : Nat.Partition 6) :
    p.toFinsuppAntidiag ∈ weightedMenu := by
  apply Finset.mem_filter.mpr
  refine ⟨p.toFinsuppAntidiag_mem_finsuppAntidiag, ?_⟩
  intro i
  change i.val + 1 ∣ p.parts.count (i.val + 1) * (i.val + 1)
  exact dvd_mul_left (i.val + 1) (p.parts.count (i.val + 1))

private def evenEncode (p : EvenPartition 6) : ↥evenMenu :=
  ⟨p.val.toFinsuppAntidiag, Finset.mem_filter.mpr
    ⟨weighted_mem p.val, by rw [decoded_card]; exact p.property⟩⟩

private theorem evenEncode_injective : Function.Injective evenEncode := by
  intro p q he
  apply Subtype.ext
  exact Nat.Partition.toFinsuppAntidiag_injective 6 (congrArg Subtype.val he)

private def splitEncode (p : SplitPartition 6) : ↥splitMenu := by
  refine ⟨p.val.toFinsuppAntidiag, Finset.mem_filter.mpr ⟨weighted_mem p.val, ?_⟩⟩
  constructor
  · intro i
    rw [decoded_count p.val (i.val + 1) (by omega)]
    exact Multiset.nodup_iff_count_le_one.mp p.property.1 (i.val + 1)
  · intro i hi
    have hnot : i.val + 1 ∉ p.val.parts := by
      intro hm
      exact (Nat.not_even_iff_odd.mpr (p.property.2 (i.val + 1) hm)) hi
    change p.val.parts.count (i.val + 1) * (i.val + 1) = 0
    rw [Multiset.count_eq_zero_of_notMem hnot, zero_mul]

private theorem splitEncode_injective : Function.Injective splitEncode := by
  intro p q he
  apply Subtype.ext
  exact Nat.Partition.toFinsuppAntidiag_injective 6 (congrArg Subtype.val he)

theorem even_partition_card_le_six : Nat.card (EvenPartition 6) ≤ 6 := by
  have hb := Nat.card_le_card_of_injective evenEncode evenEncode_injective
  rw [Nat.card_eq_finsetCard, evenMenu_card] at hb
  exact hb

theorem split_partition_card_le_one : Nat.card (SplitPartition 6) ≤ 1 := by
  have hb := Nat.card_le_card_of_injective splitEncode splitEncode_injective
  rw [Nat.card_eq_finsetCard, splitMenu_card] at hb
  exact hb

theorem alternating_six_class_card_le_seven :
    Nat.card (ConjClasses (alternatingGroup (Fin 6))) ≤ 7 := by
  have hb := class_card_le_even_add_split (Equiv.swap (0 : Fin 6) 1)
    (Equiv.Perm.sign_swap (by decide : (0 : Fin 6) ≠ 1))
  simp only [Fintype.card_fin] at hb
  exact hb.trans (by
    have he := even_partition_card_le_six
    have hs := split_partition_card_le_one
    omega)

end SymmetricSubgroupAsymptotics.AlternatingSixClassBound
