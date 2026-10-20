import SymmetricSubgroupAsymptotics.NaturalThreeNormalClassification
import SymmetricSubgroupAsymptotics.PrimeCharacterOrderDivisibility
import SymmetricSubgroupAsymptotics.PrimeRelativeCharacters

/-! A proper normal subgroup of a twelve-element binary extension of S3
has order dividing six. Its ambient binary relative head is at most one.
Only Lagrange arithmetic and the checked S3 normal trichotomy are used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.DihedralTwelveProperNormalHead
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem card_dvd_six {B : Type} [Group B] [Finite B]
    (beta : B →* Equiv.Perm (Fin 3)) (hbeta : Function.Surjective beta)
    (hB : Nat.card B=12) (hker : Nat.card beta.ker=2)
    (M : Subgroup B) [M.Normal] (hne : M≠⊤) : Nat.card M ∣ 6 := by
  have hd : Nat.card M ∣ 12 := hB ▸ M.card_subgroup_dvd_card
  have hp : Nat.card M≤12 := Nat.le_of_dvd (by decide) hd
  have h12 : Nat.card M≠12 := fun h => hne (M.eq_top_of_card_eq (h.trans hB.symm))
  have h4 : Nat.card M≠4 := by
    intro hm
    let I := M.map beta
    letI : I.Normal := Subgroup.Normal.map inferInstance beta hbeta
    have hi : Nat.card I ∣ 4 := hm ▸ M.card_map_dvd beta
    rcases NaturalThreeNormalClassification.normal_trichotomy I inferInstance with hb | ha | ht
    · have hle : M≤beta.ker := (Subgroup.map_eq_bot_iff (H := M)).mp hb
      have hc := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
      rw [hm,hker] at hc
      omega
    · have hc : Nat.card (alternatingGroup (Fin 3))=3 := by
        rw [nat_card_alternatingGroup,Nat.card_fin]
        decide
      rw [ha,hc] at hi
      norm_num at hi
    · rw [ht,Nat.card_congr Subgroup.topEquiv.toEquiv,Nat.card_perm,Nat.card_fin] at hi
      norm_num at hi
  interval_cases hn : Nat.card M <;> norm_num at *

theorem relative_head_le_one {B : Type} [Group B] [Finite B]
    (beta : B →* Equiv.Perm (Fin 3)) (hbeta : Function.Surjective beta)
    (hB : Nat.card B=12) (hker : Nat.card beta.ker=2)
    (M : Subgroup B) [M.Normal] (hne : M≠⊤) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 M)≤1 := by
  have hd := (primeCharacters_pow_finrank_dvd_card 2 M).trans
    (card_dvd_six beta hbeta hB hker M hne)
  have hdim : Module.finrank (ZMod 2) (PrimeCharacters 2 M)≤1 := by
    by_contra hn
    have htwo : 2≤Module.finrank (ZMod 2) (PrimeCharacters 2 M) := by omega
    have hfour : 4∣6 := (Nat.pow_dvd_pow 2 htwo).trans hd
    norm_num at hfour
  exact (Submodule.finrank_le _).trans hdim

end SymmetricSubgroupAsymptotics.DihedralTwelveProperNormalHead
