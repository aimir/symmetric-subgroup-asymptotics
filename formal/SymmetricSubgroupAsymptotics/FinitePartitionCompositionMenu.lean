import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Finite.Card

/-! A computable partition menu obtained from the actual positive lists.
Adjoining one or increasing the first part generates the 128 degree-eight
compositions directly, avoiding dependent casts in the cut-set equivalence.
No group or action is enumerated. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.FinitePartitionCompositionMenu

private def bump : List ℕ → List ℕ
  | [] => []
  | a :: l => (a+1) :: l

def listMenu : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | n+1 => ((listMenu n).image (List.cons 1)) ∪
      (((listMenu n).filter (fun l => l ≠ [])).image bump)

private theorem mem_listMenu (n : ℕ) (l : List ℕ)
    (hp : ∀ i ∈ l, 0 < i) (hs : l.sum = n) : l ∈ listMenu n := by
  induction n generalizing l with
  | zero =>
    cases l with
    | nil => exact Finset.mem_singleton_self _
    | cons a l =>
      have ha := hp a (List.mem_cons_self)
      simp only [List.sum_cons] at hs
      omega
  | succ n ih =>
    cases l with
    | nil => simp only [List.sum_nil] at hs; omega
    | cons a l =>
      have ha := hp a List.mem_cons_self
      have htail : ∀ i ∈ l, 0 < i := fun i hi => hp i (List.mem_cons_of_mem a hi)
      cases a with
      | zero => omega
      | succ a =>
        by_cases hz : a = 0
        · subst a
          have hs' : l.sum = n := by simp only [List.sum_cons] at hs; omega
          exact Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨l, ih l htail hs', rfl⟩)
        · have hp' : ∀ i ∈ a :: l, 0 < i := by
            intro i hi
            rcases List.mem_cons.mp hi with rfl | hi
            · omega
            · exact htail i hi
          have hs' : (a :: l).sum = n := by
            simp only [List.sum_cons] at hs ⊢
            omega
          exact Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨a :: l, Finset.mem_filter.mpr ⟨ih _ hp' hs', by simp⟩, rfl⟩)

def menu (n : ℕ) : Finset (Multiset ℕ) :=
  (listMenu n).image (fun l : List ℕ => (l : Multiset ℕ))

theorem mem_menu (n : ℕ) (p : Nat.Partition n) : p.parts ∈ menu n := by
  have h (m : Multiset ℕ) :
      (∀ i ∈ m, 0 < i) → m.sum = n → m ∈ menu n := by
    induction m using Quotient.inductionOn with
    | _ l =>
      intro hp hs
      have hpl : ∀ i ∈ l, 0 < i := by simpa only [Multiset.mem_coe] using hp
      have hsl : l.sum = n := by simpa only [Multiset.sum_coe] using hs
      exact Finset.mem_image.mpr ⟨l, mem_listMenu n l hpl hsl, rfl⟩
  exact h p.parts (fun _ hi => p.parts_pos hi) p.parts_sum

theorem partition_card_le_menu_card (n : ℕ) :
    Nat.card (Nat.Partition n) ≤ (menu n).card := by
  let f : Nat.Partition n → ↥(menu n) := fun p => ⟨p.parts, mem_menu n p⟩
  have hf : Function.Injective f := by
    intro p q he
    exact Nat.Partition.ext (congrArg Subtype.val he)
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_finsetCard] using hc

theorem menu_eight_card : (menu 8).card = 22 := by decide +kernel

end SymmetricSubgroupAsymptotics.FinitePartitionCompositionMenu
