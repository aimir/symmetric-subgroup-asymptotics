import SymmetricSubgroupAsymptotics.FinitePartitionCompositionMenu
import SymmetricSubgroupAsymptotics.AlternatingConjugacyPartitionBound

/-! The selected capacities use only positive compositions of total
mass five or seven. Literal even/split partition fibres then bound the
actual alternating class numbers, without any group enumeration. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.AlternatingSmallPartitionCompositionCapacity
open FinitePartitionCompositionMenu

def evenMenu (n : ℕ) : Finset (Multiset ℕ) :=
  (menu n).filter (fun s => Even (n+s.card))

def splitMenu (n : ℕ) : Finset (Multiset ℕ) :=
  (menu n).filter (fun s => s.Nodup ∧ ∀ a ∈ s, Odd a)

theorem menu_seven_card : (menu 7).card = 15 := by decide +kernel
theorem even_five_card : (evenMenu 5).card = 4 := by decide +kernel
theorem split_five_card : (splitMenu 5).card = 1 := by decide +kernel
theorem even_seven_card : (evenMenu 7).card = 8 := by decide +kernel
theorem split_seven_card : (splitMenu 7).card = 1 := by decide +kernel

noncomputable section
open scoped Classical
open AlternatingConjugacyPartitionBound DistinctOddPartitionInjection

private theorem even_card_le (n : ℕ) :
    Nat.card (EvenPartition n) ≤ (evenMenu n).card := by
  let f : EvenPartition n → ↥(evenMenu n) := fun p =>
    ⟨p.val.parts, Finset.mem_filter.mpr ⟨mem_menu n p.val, p.property⟩⟩
  have hf : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    exact Nat.Partition.ext (congrArg Subtype.val he)
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_finsetCard] using hc

private theorem split_card_le (n : ℕ) :
    Nat.card (SplitPartition n) ≤ (splitMenu n).card := by
  let f : SplitPartition n → ↥(splitMenu n) := fun p =>
    ⟨p.val.parts, Finset.mem_filter.mpr ⟨mem_menu n p.val, p.property⟩⟩
  have hf : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    exact Nat.Partition.ext (congrArg Subtype.val he)
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_finsetCard] using hc

theorem class_card_le_menus (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (ConjClasses (alternatingGroup (Fin n))) ≤
      (evenMenu n).card + (splitMenu n).card := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro he
    have hv := congrArg Fin.val he
    change 0 = 1 at hv
    omega
  have hb := class_card_le_even_add_split (Equiv.swap a b)
    (Equiv.Perm.sign_swap hab)
  simp only [Fintype.card_fin] at hb
  exact hb.trans (Nat.add_le_add (even_card_le n) (split_card_le n))

theorem alternating_five_class_card_le :
    Nat.card (ConjClasses (alternatingGroup (Fin 5))) ≤ 5 := by
  simpa only [even_five_card, split_five_card, Nat.reduceAdd] using
    class_card_le_menus 5 (by decide)

theorem alternating_seven_class_card_le :
    Nat.card (ConjClasses (alternatingGroup (Fin 7))) ≤ 9 := by
  simpa only [even_seven_card, split_seven_card, Nat.reduceAdd] using
    class_card_le_menus 7 (by decide)

end
end SymmetricSubgroupAsymptotics.AlternatingSmallPartitionCompositionCapacity
