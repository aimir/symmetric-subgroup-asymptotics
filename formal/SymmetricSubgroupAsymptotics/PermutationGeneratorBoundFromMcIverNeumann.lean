import SymmetricSubgroupAsymptotics.McIverNeumannPermutationSection
import SymmetricSubgroupAsymptotics.Non2PreE7SmallOrderSemisimple
import SymmetricSubgroupAsymptotics.Non2PreE7B6RankTailSource

/-! The weaker all-subgroup generator bound follows from the sharp
McIver--Neumann input already used by the final assembly. The sole
three-point exception is handled internally by the actual group order.
No additional published generator statement is imported. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

/-- McIver--Neumann implies the rounded all-subgroup bound, including the
full three-point symmetric group. -/
theorem permutationSubgroupGeneratorBound_of_mcIverNeumann
    (hMN : McIverNeumannPermutationGeneratorBound) :
    PermutationSubgroupGeneratorBound := by
  intro b J
  by_cases hb : b = 3
  · subst b
    obtain ⟨S, hS, hpow⟩ := exists_generating_finset_two_pow_le J
    have hcard : Nat.card J ≤ 6 := by
      have h := Nat.card_le_card_of_injective
        (Subtype.val : J → Equiv.Perm (Fin 3)) Subtype.val_injective
      simpa only [Nat.card_perm, Nat.card_fin] using h
    have hsmall : S.card ≤ 2 := by
      by_contra hn
      have hthree : 3 ≤ S.card := by omega
      have hp : (2 : ℕ)^3 ≤ 2^S.card :=
        Nat.pow_le_pow_right (by decide) hthree
      have hbad := hp.trans (hpow.trans hcard)
      norm_num at hbad
    exact ⟨S, hS, by omega⟩
  · obtain ⟨S, hS, hcard⟩ := hMN b J (fun h => (hb h).elim)
    exact ⟨S, hS, by omega⟩

end SymmetricSubgroupAsymptotics
