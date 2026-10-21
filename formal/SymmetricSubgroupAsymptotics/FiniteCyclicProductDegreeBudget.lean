import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Numerical degree budget for a nontrivial product of cyclic regular
actions. At least two factors of order at least two have total regular
sum at most six whenever the original product order is eight or nine. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics

private theorem twice_add_le_mul_add_four {a b : ℕ} (ha : 2≤a) (hb : 2≤b) :
    2*a+2*b≤a*b+4 := by
  obtain ⟨x,rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨y,rfl⟩ := Nat.exists_eq_add_of_le hb
  nlinarith [Nat.zero_le (x*y)]

private theorem twice_left_add_right_le_mul {a b : ℕ} (ha : 2≤a) (hb : 4≤b) :
    2*a+b≤a*b := by
  obtain ⟨x,rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨y,rfl⟩ := Nat.exists_eq_add_of_le hb
  nlinarith [Nat.zero_le (x*y)]

theorem twice_sum_le_prod_add_four {I : Type} (n : I→ℕ) :
    ∀ s : Finset I,(∀ i∈s,2≤n i) → 2≤s.card →
      2*(∑ i∈s,n i)≤(∏ i∈s,n i)+4 := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro _ hc;simp at hc
  | @insert i s hi ih =>
      intro hn hc
      have hni : 2≤n i := hn i (Finset.mem_insert_self i s)
      have hns : ∀ j∈s,2≤n j := fun j hj => hn j (Finset.mem_insert_of_mem hj)
      by_cases hs : 2≤s.card
      · have hh := ih hns hs
        have hp := Finset.pow_card_le_prod s n 2 hns
        have h4 : 4≤∏ j∈s,n j :=
          (show 4≤2^s.card from pow_le_pow_right₀ (by decide : (1 : ℕ)≤2) hs).trans hp
        have hb := twice_left_add_right_le_mul hni h4
        simp only [Finset.sum_insert hi,Finset.prod_insert hi]
        omega
      · have hs1 : s.card=1 := by rw [Finset.card_insert_of_notMem hi] at hc;omega
        obtain ⟨j,hj⟩ := Finset.card_eq_one.mp hs1
        have hnj : 2≤n j := hns j (by rw [hj];exact Finset.mem_singleton_self j)
        have hb := twice_add_le_mul_add_four hni hnj
        have hij : i ≠ j := by
          intro he
          apply hi
          rw [he,hj]
          exact Finset.mem_singleton_self j
        simpa only [hj,Finset.sum_pair hij,Finset.prod_pair hij,Nat.mul_add] using hb

/-- This is a sum-degree statement; it never multiplies action degrees
whose original group factors are already independent coordinates. -/
theorem cyclicProduct_sum_le_six_of_order_eight_or_nine
    {I : Type} [Fintype I] (n : I→ℕ) (hn : ∀ i,2≤n i)
    (hI : 2≤Fintype.card I) (hprod : (∏ i,n i)=8 ∨ (∏ i,n i)=9) :
    (∑ i,n i)≤6 := by
  have h := twice_sum_le_prod_add_four n Finset.univ (fun i _ => hn i) (by simpa using hI)
  change 2*(∑ i,n i)≤(∏ i,n i)+4 at h
  rcases hprod with hp|hp <;> rw [hp] at h <;> omega

end SymmetricSubgroupAsymptotics
