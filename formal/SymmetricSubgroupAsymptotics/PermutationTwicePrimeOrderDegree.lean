import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Finite.Defs
import Lean.Elab.Tactic.Omega

/-! The cycle lengths of the SAME permutation pay for a factor two and
an odd prime in its order. Either one cycle contains both factors, or a
prime-divisible cycle and a separate even cycle occupy at least p+2
points. This is an order-of-element obstruction, stronger here than a
prime divisor of the ambient group's cardinality. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PermutationTwicePrimeOrderDegree

theorem exists_mem_of_prime_dvd_lcm (p : ℕ) (hp : p.Prime)
    (s : Multiset ℕ) (hd : p ∣ s.lcm) : ∃ a ∈ s, p ∣ a := by
  induction s using Multiset.induction_on with
  | empty =>
    exact False.elim (hp.not_dvd_one (by simpa only [Multiset.lcm_zero] using hd))
  | cons a s ih =>
    have h : p ∣ Nat.lcm a s.lcm := by
      simpa only [Multiset.lcm_cons,lcm_eq_nat_lcm] using hd
    rcases hp.dvd_lcm.mp h with ha | hs
    · exact ⟨a,Multiset.mem_cons_self _ _,ha⟩
    · obtain ⟨b,hb,hpb⟩ := ih hs
      exact ⟨b,Multiset.mem_cons_of_mem hb,hpb⟩

theorem prime_add_two_le_card_of_twice_prime_dvd_orderOf {X : Type*} [Finite X]
    (sigma : Equiv.Perm X) (p : ℕ) (hp : p.Prime) (hcop : Nat.Coprime 2 p)
    (hdiv : 2*p ∣ orderOf sigma) : p+2 ≤ Nat.card X := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  rw [Nat.card_eq_fintype_card]
  have hporder : p ∣ orderOf sigma :=
    (show p ∣ 2*p from ⟨2,Nat.mul_comm 2 p⟩).trans hdiv
  have h2order : 2 ∣ orderOf sigma := (show 2 ∣ 2*p from ⟨p,rfl⟩).trans hdiv
  obtain ⟨a,ha,hpa⟩ := exists_mem_of_prime_dvd_lcm p hp sigma.cycleType
    (by simpa only [Equiv.Perm.lcm_cycleType] using hporder)
  have ha2 : 2 ≤ a := Equiv.Perm.two_le_of_mem_cycleType ha
  have hple : p ≤ a := Nat.le_of_dvd (by omega) hpa
  obtain ⟨s,hs⟩ := Multiset.exists_cons_of_mem ha
  have hsum : a+s.sum ≤ Fintype.card X := by
    simpa only [hs,Multiset.sum_cons] using sigma.sum_cycleType_le
  by_cases h2a : 2 ∣ a
  · have hboth : 2*p ∣ a := hcop.mul_dvd_of_dvd_of_dvd h2a hpa
    have hle : 2*p ≤ a := Nat.le_of_dvd (by omega) hboth
    have hp2 := hp.two_le
    omega
  · have h2 : 2 ∣ Nat.lcm a s.lcm := by
      simpa only [←Equiv.Perm.lcm_cycleType,hs,Multiset.lcm_cons,lcm_eq_nat_lcm]
        using h2order
    have h2s : 2 ∣ s.lcm := (Nat.prime_two.dvd_lcm.mp h2).resolve_left h2a
    obtain ⟨b,hb,_⟩ := exists_mem_of_prime_dvd_lcm 2 Nat.prime_two s h2s
    have hbfull : b ∈ sigma.cycleType := by
      rw [hs]
      exact Multiset.mem_cons_of_mem hb
    have hb2 : 2 ≤ b := Equiv.Perm.two_le_of_mem_cycleType hbfull
    obtain ⟨u,hu⟩ := Multiset.exists_cons_of_mem hb
    have htail : 2 ≤ s.sum := by rw [hu,Multiset.sum_cons]; omega
    omega

theorem nine_le_card_of_fourteen_dvd_orderOf {X : Type*} [Finite X]
    (sigma : Equiv.Perm X) (hdiv : 14 ∣ orderOf sigma) : 9 ≤ Nat.card X :=
  prime_add_two_le_card_of_twice_prime_dvd_orderOf sigma 7 (by decide) (by decide) hdiv

end SymmetricSubgroupAsymptotics.PermutationTwicePrimeOrderDegree
