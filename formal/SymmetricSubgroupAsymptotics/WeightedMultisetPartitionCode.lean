import SymmetricSubgroupAsymptotics.WeightedMultisetPartitionExpansion
import SymmetricSubgroupAsymptotics.PartitionFamilyCompositionBound

/-! For a fixed expanded label multiset, positive weighted block data
inject into the actual partitions of each label multiplicity. This
retains correlations between all repeated labels and supplies a finite
code without a canonical choice of block decomposition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.WeightedMultisetPartitionCode
open WeightedMultisetPartitionExpansion
variable {α : Type*}

def Data (F : Multiset α) :=
  {B : Multiset (α × ℕ) // (∀ b ∈ B, 0 < b.2) ∧ expand B = F}

theorem label_mem {F : Multiset α} (B : Data F) (b : α × ℕ) (hb : b ∈ B.val) :
    b.1 ∈ F := by
  have hm : b.1 ∈ expand B.val :=
    Multiset.mem_bind.mpr ⟨b, hb,
      Multiset.mem_replicate.mpr ⟨Nat.ne_of_gt (B.property.1 b hb), rfl⟩⟩
  exact B.property.2 ▸ hm

def partitionCode (F : Multiset α) (B : Data F) :
    (a : F.toFinset) → Nat.Partition (F.count a.val) := fun a => {
  parts := partsAt B.val a.val
  parts_pos := by
    intro n hn
    exact partsAt_positive B.val B.property.1 a.val n hn
  parts_sum := by rw [← count_expand, B.property.2] }

theorem partsAt_eq_zero_of_not_mem {F : Multiset α} (B : Data F) (a : α)
    (ha : a ∉ F) : partsAt B.val a = 0 := by
  apply Multiset.eq_zero_of_forall_notMem
  intro n hn
  obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp hn
  obtain ⟨hb, hba⟩ := Multiset.mem_filter.mp hb
  exact ha (hba ▸ label_mem B b hb)

theorem partitionCode_injective (F : Multiset α) :
    Function.Injective (partitionCode F) := by
  intro B C he
  apply Subtype.ext
  apply partsAt_injective
  intro a
  by_cases ha : a ∈ F
  · let aF : F.toFinset := ⟨a, Multiset.mem_toFinset.mpr ha⟩
    exact congrArg (fun p : Nat.Partition (F.count a) => p.parts) (congrFun he aF)
  · rw [partsAt_eq_zero_of_not_mem B a ha, partsAt_eq_zero_of_not_mem C a ha]

instance dataFinite (F : Multiset α) : Finite (Data F) :=
  Finite.of_injective (partitionCode F) (partitionCode_injective F)

theorem partition_family_card_le (F : Multiset α) :
    Nat.card ((a : F.toFinset) → Nat.Partition (F.count a.val)) ≤ 2^(F.card-1) := by
  by_cases hF : F = 0
  · subst F
    simp
  · obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hF
    letI : Nonempty (F.toFinset : Type _) := ⟨⟨a, Multiset.mem_toFinset.mpr ha⟩⟩
    have hs : (∑ a : F.toFinset, F.count a.val) = F.card := by
      calc
        _ = ∑ a ∈ F.toFinset, F.count a :=
          F.toFinset.sum_coe_sort (fun a : α => F.count a)
        _ = F.card := Multiset.toFinset_sum_count_eq F
    have hp (a : F.toFinset) : 0 < F.count a.val :=
      Multiset.count_pos.mpr (Multiset.mem_toFinset.mp a.property)
    simpa only [hs] using
      PartitionFamilyCompositionBound.partition_family_card_le (fun a : F.toFinset =>
        F.count a.val) hp

theorem data_card_le (F : Multiset α) : Nat.card (Data F) ≤ 2^(F.card-1) :=
  (Nat.card_le_card_of_injective (partitionCode F) (partitionCode_injective F)).trans
    (partition_family_card_le F)

end SymmetricSubgroupAsymptotics.WeightedMultisetPartitionCode
