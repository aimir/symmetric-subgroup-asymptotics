import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSymmetricTop
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSymmetricAbelianization
import SymmetricSubgroupAsymptotics.KovacsPraegerAbelianization
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadChain

/-! Every proper normal subgroup of an actual order-two extension of S4
has at most one binary relative-head position. The proper-image branch
uses the checked zero head of proper S4 normals; the full-image branch
is isomorphic to S4. No normal-subgroup enumeration is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.DoubleSymmetricFourProperNormalHead
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem symmetric_character_rank :
    Module.finrank (ZMod 2) (PrimeCharacters 2 (Equiv.Perm (Fin 4)))≤1 := by
  have h := primeCharacters_two_mul_three_le_abelianization (Equiv.Perm (Fin 4))
  have hc : Nat.card (PrimeCharacters 2 (Equiv.Perm (Fin 4)))≤2 :=
    (Nat.le_mul_of_pos_right _ (Nat.card_pos :
      0<Nat.card (PrimeCharacters 3 (Equiv.Perm (Fin 4))))).trans
      (h.trans TwelvePointRemainingStructural.symmetric_abelianization_card_le_two)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mp hc

 theorem relative_head_le_one {B : Type} [Group B] [Finite B]
    (beta : B →* Equiv.Perm (Fin 4)) (hbeta : Function.Surjective beta)
    (hker : Nat.card beta.ker=2)
    (M : Subgroup B) [M.Normal] (hne : M≠⊤) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 M)≤1 := by
  have hs : Nat.card (Equiv.Perm (Fin 4))=24 := by rw [Nat.card_perm,Nat.card_fin]; decide
  have hq : Nat.card (B ⧸ beta.ker)=24 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective beta hbeta).toEquiv,hs]
  have hB : Nat.card B=48 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup beta.ker
    rw [hq,hker] at h
    exact h
  let I := M.map beta
  letI : I.Normal := Subgroup.Normal.map inferInstance beta hbeta
  by_cases hfull : I=⊤
  · let f : M →* Equiv.Perm (Fin 4) := beta.comp M.subtype
    have hf : Function.Surjective f := by
      intro y
      have hy : y∈I := by rw [hfull]; trivial
      obtain ⟨x,hx,hxy⟩ := hy
      exact ⟨⟨x,hx⟩,hxy⟩
    have hquot : Nat.card (M ⧸ f.ker)=24 := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,hs]
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [hquot] at hcard
    have hle : Nat.card M≤48 := by
      simpa only [hB] using Nat.card_le_card_of_injective M.subtype Subtype.val_injective
    have hnot : Nat.card M≠48 := fun h => hne (M.eq_top_of_card_eq (h.trans hB.symm))
    have hp : 0<Nat.card f.ker := Nat.card_pos
    have hone : Nat.card f.ker=1 := by omega
    have hinj : Function.Injective f :=
      (MonoidHom.ker_eq_bot_iff f).mp (f.ker.eq_bot_of_card_eq hone)
    let e : M ≃* Equiv.Perm (Fin 4) := MulEquiv.ofBijective f ⟨hinj,hf⟩
    exact (Submodule.finrank_le _).trans
      ((primeCharacter_finrank_congr 2 e).le.trans symmetric_character_rank)
  · let e := QuotientGroup.quotientKerEquivOfSurjective beta hbeta
    have he : (normalChainQuotient beta.ker M).map e.toMonoidHom=I := by
      change (M.map (QuotientGroup.mk' beta.ker)).map e.toMonoidHom=M.map beta
      rw [Subgroup.map_map]
      rfl
    have hz : Module.finrank (ZMod 2)
        (primeRelativeCharacters 2 (normalChainQuotient beta.ker M))=0 :=
      (relativeCharacterAmbientCongr 2 e (normalChainQuotient beta.ker M) I he).finrank_eq.symm.trans
        (TwelvePointRemainingStructural.proper_normal_binary_relative_head_zero I hfull)
    have hi : Module.finrank (ZMod 2) (primeRelativeCharacters 2 (M ⊓ beta.ker))≤1 := by
      have hc : Nat.card (M ⊓ beta.ker : Subgroup B)≤2 := by
        simpa only [hker] using Nat.card_le_card_of_injective
          (Subgroup.inclusion (inf_le_right : M ⊓ beta.ker≤beta.ker))
          (Subgroup.inclusion_injective (inf_le_right : M ⊓ beta.ker≤beta.ker))
      have hd := (primeCharacters_pow_finrank_le_card 2 (M ⊓ beta.ker : Subgroup B)).trans hc
      have hr : Module.finrank (ZMod 2) (PrimeCharacters 2 (M ⊓ beta.ker : Subgroup B))≤1 :=
        (Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mp hd
      exact (Submodule.finrank_le _).trans hr
    have hc := primeRelativeHead_chain_le (M ⊓ beta.ker) M 2 inf_le_left
    rw [primeRelativeHead_second_isomorphism 2 M beta.ker,hz,Nat.add_zero] at hc
    exact hc.trans hi

end SymmetricSubgroupAsymptotics.DoubleSymmetricFourProperNormalHead
