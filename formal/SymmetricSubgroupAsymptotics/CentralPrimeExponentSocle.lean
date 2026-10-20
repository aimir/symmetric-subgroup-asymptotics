import SymmetricSubgroupAsymptotics.NormalDisjointQuotientSocle
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Coset.Card

/-! A central subgroup of prime exponent is contained in the actual socle.
Combined with a maximal disjoint normal quotient, this identifies that
quotient's entire socle with the unchanged image of the original subgroup. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CentralPrimeExponentSocle

variable {G : Type} [Group G] [Finite G]

theorem normal_of_le_center (A : Subgroup G) (hA : A ≤ Subgroup.center G) :
    A.Normal := ⟨by
  intro a ha g
  have hc := Subgroup.mem_center_iff.mp (hA ha) g
  simpa only [hc, mul_assoc, mul_inv_cancel, mul_one] using ha⟩

theorem le_socle (p : ℕ) [Fact p.Prime] (A : Subgroup G)
    (hcentral : A ≤ Subgroup.center G) (hpow : ∀ a : A, (a : G) ^ p = 1) :
    A ≤ finiteGroupSocle G := by
  intro a ha
  by_cases hane : a = 1
  · simpa only [hane] using (finiteGroupSocle G).one_mem
  let M := Subgroup.zpowers a
  have hMA : M ≤ A := by
    intro x hx
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact A.zpow_mem ha z
  have hMN : M.Normal := normal_of_le_center M (hMA.trans hcentral)
  have hcard : Nat.card M = p := by
    exact (Nat.card_zpowers a).trans (orderOf_eq_prime (hpow ⟨a, ha⟩) hane)
  have hMne : M ≠ ⊥ := by
    intro h
    exact hane (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_zpowers a))
  have hminimal : IsMinimalNormalSubgroup M := by
    refine ⟨hMN, hMne, ?_⟩
    intro K _ hKne hKM
    have hdvd : Nat.card K ∣ p := hcard ▸ Subgroup.card_dvd_of_le hKM
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with hk | hk
    · exact False.elim (hKne (K.eq_bot_of_card_eq hk))
    · exact Subgroup.eq_of_le_of_card_ge hKM (by rw [hcard, hk])
  exact Subgroup.subset_normalClosure ⟨M, hminimal, Subgroup.mem_zpowers a⟩

theorem map_le_center {Q : Type} [Group Q] (q : G →* Q)
    (hq : Function.Surjective q) (A : Subgroup G)
    (hcentral : A ≤ Subgroup.center G) :
    A.map q ≤ Subgroup.center Q := by
  rintro _ ⟨a, ha, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro y
  obtain ⟨g, rfl⟩ := hq y
  exact (map_mul q g a).symm.trans
    ((congrArg q (Subgroup.mem_center_iff.mp (hcentral ha) g)).trans (map_mul q a g))

theorem socle_eq_image (p : ℕ) [Fact p.Prime] (A B : Subgroup G)
    [A.Normal] [B.Normal] (hcentral : A ≤ Subgroup.center G)
    (hpow : ∀ a : A, (a : G) ^ p = 1) (hd : Disjoint A B)
    (hmax : ∀ K : Subgroup G, K.Normal → Disjoint A K → B ≤ K → K ≤ B) :
    finiteGroupSocle (G ⧸ B) = A.map (QuotientGroup.mk' B) := by
  apply le_antisymm (NormalDisjointQuotientSocle.socle_le_image A B hd hmax)
  apply le_socle p _
    (map_le_center (QuotientGroup.mk' B) (QuotientGroup.mk'_surjective B) A hcentral)
  rintro ⟨_, a, ha, rfl⟩
  rw [← map_pow, hpow ⟨a, ha⟩, map_one]

end SymmetricSubgroupAsymptotics.CentralPrimeExponentSocle

end
