import SymmetricSubgroupAsymptotics.NaturalThreeNormalClassification
import SymmetricSubgroupAsymptotics.PrimeCharacterOrderDivisibility
import SymmetricSubgroupAsymptotics.PrimeRelativeCharacters
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NaturalThreeProperBinaryRelativeHead
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem relative_head_zero (L : Subgroup (Equiv.Perm (Fin 3))) [L.Normal] (hne : L≠⊤) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 L)≤0 := by
  have hc : Nat.card L∣3 := by
    rcases NaturalThreeNormalClassification.normal_trichotomy L inferInstance with hb | ha | ht
    · rw [hb]
      simp [Nat.card_eq_fintype_card]
    · rw [ha,nat_card_alternatingGroup,Nat.card_fin]
      decide
    · exact False.elim (hne ht)
  have hd := (primeCharacters_pow_finrank_dvd_card 2 L).trans hc
  have hr : Module.finrank (ZMod 2) (PrimeCharacters 2 L)=0 := by
    by_contra hn
    have hp : 1≤Module.finrank (ZMod 2) (PrimeCharacters 2 L) := Nat.one_le_iff_ne_zero.mpr hn
    have hp2 : 2∣2^Module.finrank (ZMod 2) (PrimeCharacters 2 L) := by
      simpa using Nat.pow_dvd_pow 2 hp
    have hf : 2∣3 := hp2.trans hd
    norm_num at hf
  exact (Submodule.finrank_le _).trans hr.le
end SymmetricSubgroupAsymptotics.NaturalThreeProperBinaryRelativeHead
