import SymmetricSubgroupAsymptotics.PartitionTwoSmallestShrink
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Finite.Card

/-! Actual partitions without a part one inject into partitions two
smaller. The two least parts are shrunk, with a separate singleton rule;
the checked list inverse retains all multiplicity information. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PartitionNoOneShrink
open PartitionTwoSmallestShrink

abbrev NoOnes (n : ℕ) := {p : Nat.Partition n // 1 ∉ p.parts}

def sortedParts {n : ℕ} (p : NoOnes n) : List ℕ := p.val.parts.sort (· ≤ ·)

theorem sortedParts_ge_two {n : ℕ} (p : NoOnes n) :
    ∀ a ∈ sortedParts p, 2 ≤ a := by
  intro a ha
  have hm : a ∈ p.val.parts := (Multiset.mem_sort (· ≤ ·)).mp ha
  have hp := p.val.parts_pos hm
  have hn : a ≠ 1 := by intro h; subst a; exact p.property hm
  omega

theorem sortedParts_sum {n : ℕ} (p : NoOnes n) : (sortedParts p).sum = n := by
  have h := congrArg Multiset.sum (Multiset.sort_eq p.val.parts (· ≤ ·))
  simpa only [Multiset.sum_coe, p.val.parts_sum] using h

theorem sortedParts_ne_nil {n : ℕ} (hn : 2 ≤ n) (p : NoOnes n) :
    sortedParts p ≠ [] := by
  intro he
  have h := sortedParts_sum p
  rw [he, List.sum_nil] at h
  omega

def shrinkPartition {n : ℕ} (hn : 2 ≤ n) (p : NoOnes n) : Nat.Partition (n-2) where
  parts := (shrink (sortedParts p) : Multiset ℕ)
  parts_pos := by
    intro a ha
    exact shrink_positive _ (sortedParts_ge_two p) a ha
  parts_sum := by
    rw [Multiset.sum_coe]
    have h := shrink_sum_add_two _ (sortedParts_ne_nil hn p) (sortedParts_ge_two p)
    rw [sortedParts_sum] at h
    omega

theorem shrinkPartition_injective {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective (shrinkPartition hn) := by
  intro p q he
  have hparts := congrArg Nat.Partition.parts he
  change (shrink (sortedParts p) : Multiset ℕ) = ↑(shrink (sortedParts q)) at hparts
  have hp : (sortedParts p).Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have hq : (sortedParts q).Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have hl : shrink (sortedParts p) = shrink (sortedParts q) :=
    (Multiset.coe_eq_coe.mp hparts).eq_of_pairwise'
      (shrink_sorted _ hp) (shrink_sorted _ hq)
  have hs := shrink_injective_on _ _ (sortedParts_ne_nil hn p)
    (sortedParts_ne_nil hn q) (sortedParts_ge_two p) (sortedParts_ge_two q) hl
  apply Subtype.ext
  apply Nat.Partition.ext
  have hc := congrArg (fun l : List ℕ => (l : Multiset ℕ)) hs
  simpa only [sortedParts, Multiset.sort_eq] using hc

theorem noOnes_card_le {n : ℕ} (hn : 2 ≤ n) :
    Nat.card (NoOnes n) ≤ Nat.card (Nat.Partition (n-2)) :=
  Nat.card_le_card_of_injective _ (shrinkPartition_injective hn)

end SymmetricSubgroupAsymptotics.PartitionNoOneShrink
