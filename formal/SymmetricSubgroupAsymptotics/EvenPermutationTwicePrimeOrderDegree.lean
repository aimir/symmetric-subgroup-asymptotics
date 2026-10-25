import SymmetricSubgroupAsymptotics.EvenCycleMultisetParity
import SymmetricSubgroupAsymptotics.PermutationTwicePrimeOrderDegree

/-! An even permutation whose actual element order contains coprime
factors2,p occupies at least p+4points. Even cycles occur in pairs. If the
prime-bearing cycle is odd there are two further even cycles; if it is
even there is one further even cycle. No action catalogue is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.EvenPermutationTwicePrimeOrderDegree
open EvenCycleMultisetParity PermutationTwicePrimeOrderDegree

private theorem le_sum_of_mem (s : Multiset ℕ) (a : ℕ) (ha : a ∈ s) : a ≤ s.sum := by
  obtain ⟨u,rfl⟩ := Multiset.exists_cons_of_mem ha
  simp only [Multiset.sum_cons]
  omega

theorem prime_add_four_le_card_of_twice_prime_dvd_orderOf {X : Type*} [Fintype X] [DecidableEq X]
    (sigma : Equiv.Perm X) (hsign : Equiv.Perm.sign sigma = 1)
    (p : ℕ) (hp : p.Prime) (hcop : Nat.Coprime 2 p)
    (hdiv : 2*p ∣ orderOf sigma) : p+4 ≤ Nat.card X := by
  classical
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
  have hfull : Even ((a ::ₘ s).sum+(a ::ₘ s).card) := by
    simpa only [hs] using cycleType_exponent_even sigma hsign
  by_cases haeven : Even a
  · obtain ⟨b,hb,_⟩ := exists_even_tail_of_even_head a s haeven hfull
    have hbfull : b ∈ sigma.cycleType := by
      rw [hs]
      exact Multiset.mem_cons_of_mem hb
    have hb2 : 2 ≤ b := Equiv.Perm.two_le_of_mem_cycleType hbfull
    have hbsum := le_sum_of_mem s b hb
    have hboth : 2*p ∣ a := hcop.mul_dvd_of_dvd_of_dvd haeven.two_dvd hpa
    have hle : 2*p ≤ a := Nat.le_of_dvd (by omega) hboth
    have hp2 := hp.two_le
    omega
  · have haodd : a%2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp haeven)
    have hfullmod := Nat.dvd_iff_mod_eq_zero.mp hfull.two_dvd
    simp only [Multiset.sum_cons,Multiset.card_cons] at hfullmod
    have htail : Even (s.sum+s.card) := by
      apply even_iff_two_dvd.mpr
      apply Nat.dvd_iff_mod_eq_zero.mpr
      omega
    have h2a : ¬2 ∣ a := fun h => haeven (even_iff_two_dvd.mpr h)
    have h2 : 2 ∣ Nat.lcm a s.lcm := by
      simpa only [←Equiv.Perm.lcm_cycleType,hs,Multiset.lcm_cons,lcm_eq_nat_lcm]
        using h2order
    have h2s : 2 ∣ s.lcm := (Nat.prime_two.dvd_lcm.mp h2).resolve_left h2a
    obtain ⟨b,hb,hbdiv⟩ := exists_mem_of_prime_dvd_lcm 2 Nat.prime_two s h2s
    have hbfull : b ∈ sigma.cycleType := by
      rw [hs]
      exact Multiset.mem_cons_of_mem hb
    have hb2 : 2 ≤ b := Equiv.Perm.two_le_of_mem_cycleType hbfull
    have hbeven : Even b := even_iff_two_dvd.mpr hbdiv
    obtain ⟨u,hu⟩ := Multiset.exists_cons_of_mem hb
    have hbtail : Even ((b ::ₘ u).sum+(b ::ₘ u).card) := by
      simpa only [hu] using htail
    obtain ⟨c,hc,_⟩ := exists_even_tail_of_even_head b u hbeven hbtail
    have hcfull : c ∈ sigma.cycleType := by
      rw [hs,hu]
      exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hc)
    have hc2 : 2 ≤ c := Equiv.Perm.two_le_of_mem_cycleType hcfull
    have hcsum := le_sum_of_mem u c hc
    have hsum' : a+(b+u.sum) ≤ Fintype.card X := by
      simpa only [hu,Multiset.sum_cons] using hsum
    omega

theorem eleven_le_card_of_fourteen_dvd_orderOf {X : Type*} [Fintype X] [DecidableEq X]
    (sigma : Equiv.Perm X) (hsign : Equiv.Perm.sign sigma = 1)
    (hdiv : 14 ∣ orderOf sigma) : 11 ≤ Nat.card X :=
  prime_add_four_le_card_of_twice_prime_dvd_orderOf sigma hsign 7 (by decide) (by decide) hdiv

end SymmetricSubgroupAsymptotics.EvenPermutationTwicePrimeOrderDegree
