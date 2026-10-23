import Mathlib.Data.List.Sort
import Lean.Elab.Tactic.Omega

/-! Shrink the two least entries of a sorted positive list by one.
The singleton case shrinks its entry by two and suppresses zero. An
explicit inverse proves injectivity on nonempty lists with entries>=2;
sorting makes this usable for partitions with no part1. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.PartitionTwoSmallestShrink

def shrink : List ℕ → List ℕ
  | [] => []
  | [a] => if a=2 then [] else [a-2]
  | a::b::l => (a-1)::(b-1)::l

def restore : List ℕ → List ℕ
  | [] => [2]
  | [a] => [a+2]
  | a::b::l => (a+1)::(b+1)::l

theorem restore_shrink (l : List ℕ) (hne : l≠[])
    (hpos : ∀a∈l,2≤a) : restore (shrink l)=l := by
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons a l =>
    cases l with
    | nil =>
      have ha2 : 2≤a := hpos a (by simp)
      by_cases ha : a=2
      · simp [shrink,restore,ha]
      · simp [shrink,restore,ha,Nat.sub_add_cancel ha2]
    | cons b l =>
      have ha1 : 1≤a := (by decide : 1≤2).trans (hpos a (by simp))
      have hb1 : 1≤b := (by decide : 1≤2).trans (hpos b (by simp))
      simp [shrink,restore,Nat.sub_add_cancel ha1,Nat.sub_add_cancel hb1]

theorem shrink_injective_on (l m : List ℕ) (hl : l≠[]) (hm : m≠[])
    (hlpos : ∀a∈l,2≤a) (hmpos : ∀a∈m,2≤a) (he : shrink l=shrink m) : l=m := by
  have h := congrArg restore he
  simpa only [restore_shrink l hl hlpos,restore_shrink m hm hmpos] using h

theorem shrink_positive (l : List ℕ) (hpos : ∀a∈l,2≤a) :
    ∀a∈shrink l,0<a := by
  cases l with
  | nil => simp [shrink]
  | cons a l =>
    cases l with
    | nil =>
      have ha2 : 2≤a := hpos a (by simp)
      by_cases ha : a=2
      · simp [shrink,ha]
      · simp only [shrink,if_neg ha,List.mem_cons,List.not_mem_nil,or_false]
        intro x hx
        subst x
        omega
    | cons b l =>
      have ha2 : 2≤a := hpos a (by simp)
      have hb2 : 2≤b := hpos b (by simp)
      intro x hx
      simp only [shrink,List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · omega
      · omega
      · exact (by decide : 0<2).trans_le (hpos x (by simp [hx]))

theorem shrink_sum_add_two (l : List ℕ) (hne : l≠[]) (hpos : ∀a∈l,2≤a) :
    (shrink l).sum+2=l.sum := by
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons a l =>
    cases l with
    | nil =>
      have ha2 : 2≤a := hpos a (by simp)
      by_cases ha : a=2 <;> simp [shrink,ha,Nat.sub_add_cancel ha2]
    | cons b l =>
      have ha2 : 2≤a := hpos a (by simp)
      have hb2 : 2≤b := hpos b (by simp)
      simp only [shrink,List.sum_cons]
      omega

theorem shrink_sorted (l : List ℕ) (hl : l.Pairwise (·≤·)) :
    (shrink l).Pairwise (·≤·) := by
  cases l with
  | nil => simp [shrink]
  | cons a l =>
    cases l with
    | nil => by_cases ha : a=2 <;> simp [shrink,ha]
    | cons b l =>
      have ha := List.pairwise_cons.mp hl
      have hb := List.pairwise_cons.mp ha.2
      apply List.pairwise_cons.mpr
      refine ⟨?_,List.pairwise_cons.mpr ⟨?_,hb.2⟩⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Nat.sub_le_sub_right (ha.1 b (by simp)) 1
        · exact (Nat.sub_le a 1).trans (ha.1 x (by simp [hx]))
      · intro x hx
        exact (Nat.sub_le b 1).trans (hb.1 x hx)

end SymmetricSubgroupAsymptotics.PartitionTwoSmallestShrink
