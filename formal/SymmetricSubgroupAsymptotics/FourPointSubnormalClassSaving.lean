import SymmetricSubgroupAsymptotics.FourPointPermutationClassBound
import SymmetricSubgroupAsymptotics.NaturalFourNormalChains
import Mathlib.GroupTheory.IndexNormal

/-! Strict class budgets for proper subnormal subgroups of literal S4.
The proof uses the actual normal chain and the index-two A4 subgroup.
There is no enumeration of subgroups or permutation actions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FourPointSubnormalClassSaving

theorem alternating_subgroup_class_card_le_four
    (H : Subgroup (alternatingGroup (Fin 4))) : Nat.card (ConjClasses H) ≤ 4 := by
  have hG : Nat.card (alternatingGroup (Fin 4)) = 12 :=
    alternatingGroup.card_of_card_eq_four (by simp)
  have hp : 0 < Nat.card H := Nat.card_pos
  have hdvd : Nat.card H ∣ 12 := by simpa only [hG] using H.card_subgroup_dvd_card
  have hcases : Nat.card H ≤ 4 ∨ Nat.card H = 6 ∨ Nat.card H = 12 := by
    obtain ⟨c,hc⟩ := hdvd
    have hcpos : 0 < c := by
      by_contra h
      have hz : c = 0 := by omega
      rw [hz,mul_zero] at hc
      omega
    have hcle : c ≤ 12 := by nlinarith
    interval_cases c <;> omega
  rcases hcases with hsmall | h6 | h12
  · exact (Nat.card_le_card_of_surjective (@ConjClasses.mk H _) ConjClasses.mk_surjective).trans hsmall
  · have hmul := H.card_mul_index
    rw [h6,hG] at hmul
    have hn : H.Normal := H.normal_of_index_eq_two (by omega)
    rcases NaturalA4ScalarFourHead.normal_subgroup_trichotomy H hn with h | h | h
    · rw [h] at h6
      simp only [Nat.card_unique] at h6
      omega
    · rw [h,alternatingGroup.kleinFour_card_of_card_eq_four (by simp)] at h6
      omega
    · have ht : Nat.card H = 12 := by
        rw [h]
        exact (Nat.card_congr (Subgroup.topEquiv :
          (⊤ : Subgroup (alternatingGroup (Fin 4))) ≃* alternatingGroup (Fin 4)).toEquiv).trans hG
      omega
  · have ht : H = ⊤ := H.eq_top_of_card_eq (h12.trans hG.symm)
    rw [ht,conjugacyClass_card_congr (Subgroup.topEquiv :
      (⊤ : Subgroup (alternatingGroup (Fin 4))) ≃* alternatingGroup (Fin 4))]
    exact FourPointClassRepresentativeCovers.alternating_class_card_le_four

theorem proper_normal_le_alternating (N : Subgroup (Equiv.Perm (Fin 4)))
    (hN : N.Normal) (hne : N ≠ ⊤) : N ≤ alternatingGroup (Fin 4) := by
  rcases NaturalFourNormalChains.symmetric_normal_total N (alternatingGroup (Fin 4)) hN
    inferInstance with h | h
  · exact h
  · rcases AlternatingTopImageNormalGenerators.above_alternating N h with h | h
    · exact h.le
    · exact (hne h).elim

theorem proper_subnormal_class_card_le_four (H : Subgroup (Equiv.Perm (Fin 4)))
    (hH : H.IsSubnormal) (hne : H ≠ ⊤) : Nat.card (ConjClasses H) ≤ 4 := by
  obtain ⟨N,hN,hHN,hNt⟩ := hH.exists_normal_and_le_and_lt_top_of_ne hne
  have hHA := hHN.trans (proper_normal_le_alternating N hN hNt.ne)
  have h := alternating_subgroup_class_card_le_four (H.subgroupOf (alternatingGroup (Fin 4)))
  rw [conjugacyClass_card_congr (Subgroup.subgroupOfEquivOfLe hHA)] at h
  exact h

end SymmetricSubgroupAsymptotics.FourPointSubnormalClassSaving
