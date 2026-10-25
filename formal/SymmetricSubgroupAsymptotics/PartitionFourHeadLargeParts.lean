import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Multiset.Sort
import SymmetricSubgroupAsymptotics.FiveSeparatedCompositionStarts

/-! Exact decomposition of an actual partition into the multiplicities of
parts one through four and the sorted composition of its larger parts.
The remaining mass is determined by the original total and these heads. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PartitionFourHeadLargeParts

def smallParts {n : ℕ} (p : Nat.Partition n) : Multiset ℕ :=
  p.parts.filter (fun a => a < 5)

def largeParts {n : ℕ} (p : Nat.Partition n) : Multiset ℕ :=
  p.parts.filter (fun a => ¬ a < 5)

def headCounts {n : ℕ} (p : Nat.Partition n) : Fin 4 → ℕ :=
  fun i => p.parts.count (i.val + 1)

def largeMass {n : ℕ} (p : Nat.Partition n) : ℕ := (largeParts p).sum

theorem small_add_large {n : ℕ} (p : Nat.Partition n) :
    smallParts p + largeParts p = p.parts :=
  Multiset.filter_add_not (fun a : ℕ => a < 5) p.parts

theorem parts_card_le {n : ℕ} (p : Nat.Partition n) : p.parts.card ≤ n := by
  obtain ⟨c,rfl⟩ := Nat.Partition.ofComposition_surj p
  simpa only [Nat.Partition.ofComposition_parts,Multiset.coe_card] using c.length_le

theorem headCounts_le {n : ℕ} (p : Nat.Partition n) (i : Fin 4) :
    headCounts p i ≤ n :=
  (Multiset.count_le_card (i.val + 1) p.parts).trans (parts_card_le p)

theorem smallParts_eq_of_headCounts_eq {n : ℕ} (p q : Nat.Partition n)
    (he : headCounts p = headCounts q) : smallParts p = smallParts q := by
  apply Multiset.ext.mpr
  intro a
  by_cases ha : a < 5
  · simp only [smallParts,Multiset.count_filter,if_pos ha]
    by_cases hz : a = 0
    · subst a
      have hp : 0 ∉ p.parts := fun h => (Nat.lt_irrefl 0) (p.parts_pos h)
      have hq : 0 ∉ q.parts := fun h => (Nat.lt_irrefl 0) (q.parts_pos h)
      rw [Multiset.count_eq_zero_of_notMem hp,Multiset.count_eq_zero_of_notMem hq]
    · let i : Fin 4 := ⟨a - 1,by omega⟩
      have hi : i.val + 1 = a := by dsimp only [i]; omega
      have h := congrFun he i
      change p.parts.count (i.val + 1) = q.parts.count (i.val + 1) at h
      simpa only [hi] using h
  · simp only [smallParts,Multiset.count_filter,if_neg ha]

theorem small_sum_add_largeMass {n : ℕ} (p : Nat.Partition n) :
    (smallParts p).sum + largeMass p = n := by
  have h := congrArg Multiset.sum (small_add_large p)
  simpa only [Multiset.sum_add,p.parts_sum,largeMass] using h

theorem largeMass_le {n : ℕ} (p : Nat.Partition n) : largeMass p ≤ n := by
  have h := small_sum_add_largeMass p
  omega

theorem largeMass_eq_of_headCounts_eq {n : ℕ} (p q : Nat.Partition n)
    (he : headCounts p = headCounts q) : largeMass p = largeMass q := by
  have hs := congrArg Multiset.sum (smallParts_eq_of_headCounts_eq p q he)
  have hp := small_sum_add_largeMass p
  have hq := small_sum_add_largeMass q
  omega

def largeComposition {n : ℕ} (p : Nat.Partition n) : Composition (largeMass p) where
  blocks := (largeParts p).sort (· ≤ ·)
  blocks_pos := by
    intro a ha
    have hm : a ∈ largeParts p := (Multiset.mem_sort (· ≤ ·)).mp ha
    have hl : ¬ a < 5 := (Multiset.mem_filter.mp hm).2
    omega
  blocks_sum := by
    have h := congrArg Multiset.sum (Multiset.sort_eq (largeParts p) (· ≤ ·))
    simpa only [Multiset.sum_coe,largeMass] using h

theorem largeComposition_parts {n : ℕ} (p : Nat.Partition n) :
    ((largeComposition p).blocks : Multiset ℕ) = largeParts p :=
  Multiset.sort_eq (largeParts p) (· ≤ ·)

theorem largeComposition_ge_five {n : ℕ} (p : Nat.Partition n) :
    ∀ a ∈ (largeComposition p).blocks, 5 ≤ a := by
  intro a ha
  have hm : a ∈ largeParts p := (Multiset.mem_sort (· ≤ ·)).mp ha
  have hl : ¬ a < 5 := (Multiset.mem_filter.mp hm).2
  omega

theorem partition_eq_of_heads_and_largeParts {n : ℕ} (p q : Nat.Partition n)
    (hh : headCounts p = headCounts q) (hl : largeParts p = largeParts q) : p = q := by
  apply Nat.Partition.ext
  rw [← small_add_large p,← small_add_large q,
    smallParts_eq_of_headCounts_eq p q hh,hl]

end SymmetricSubgroupAsymptotics.PartitionFourHeadLargeParts
