import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Ring.Parity
import Lean.Elab.Tactic.Omega

/-! Generic cycle parity bookkeeping. An even permutation has even
sum-plus-cardinality of its actual cycle lengths. Consequently, removing
one even cycle still leaves another even cycle. No finite action or
matrix data is involved. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.EvenCycleMultisetParity

theorem even_sum_add_card_of_odd (s : Multiset ℕ) :
    (∀ a ∈ s, Odd a) → Even (s.sum+s.card) := by
  induction s using Multiset.induction_on with
  | empty => intro _; exact ⟨0,rfl⟩
  | cons a s ih =>
    intro hodd
    have ha : a%2 = 1 := Nat.odd_iff.mp (hodd a (Multiset.mem_cons_self _ _))
    have ht : (s.sum+s.card)%2 = 0 := Nat.dvd_iff_mod_eq_zero.mp
      (ih (fun b hb => hodd b (Multiset.mem_cons_of_mem hb))).two_dvd
    apply even_iff_two_dvd.mpr
    apply Nat.dvd_iff_mod_eq_zero.mpr
    simp only [Multiset.sum_cons,Multiset.card_cons]
    omega

theorem exists_even_tail_of_even_head (a : ℕ) (s : Multiset ℕ)
    (ha : Even a) (hfull : Even ((a ::ₘ s).sum+(a ::ₘ s).card)) :
    ∃ b ∈ s, Even b := by
  by_contra h
  have hodd : ∀ b ∈ s, Odd b := by
    intro b hb
    apply Nat.not_even_iff_odd.mp
    exact fun he => h ⟨b,hb,he⟩
  have ht : (s.sum+s.card)%2 = 0 := Nat.dvd_iff_mod_eq_zero.mp
    (even_sum_add_card_of_odd s hodd).two_dvd
  have hamod : a%2 = 0 := Nat.dvd_iff_mod_eq_zero.mp ha.two_dvd
  have hmod := Nat.dvd_iff_mod_eq_zero.mp hfull.two_dvd
  simp only [Multiset.sum_cons,Multiset.card_cons] at hmod
  omega

theorem cycleType_exponent_even {X : Type*} [Fintype X] [DecidableEq X]
    (sigma : Equiv.Perm X) (hsign : Equiv.Perm.sign sigma = 1) :
    Even (sigma.cycleType.sum+sigma.cycleType.card) := by
  have hunit : (-1 : ℤˣ)^(sigma.cycleType.sum+sigma.cycleType.card) = 1 :=
    (Equiv.Perm.sign_of_cycleType sigma).symm.trans hsign
  have hint : (-1 : ℤ)^(sigma.cycleType.sum+sigma.cycleType.card) = 1 := by
    simpa only [Units.val_pow_eq_pow_val] using congrArg (fun u : ℤˣ => (u : ℤ)) hunit
  exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤ) ≠ 1)).mp hint

end SymmetricSubgroupAsymptotics.EvenCycleMultisetParity
