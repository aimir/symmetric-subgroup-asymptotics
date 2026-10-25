import SymmetricSubgroupAsymptotics.PrimitiveSocleEightPointTitsExclusion

/-! The SAME positive Sylow intersection already supplies a subgroup
of the actual Tits model whose order is a power of two at least512.
Its order divisibility excludes faithful actions, and simple socle
factors, on at most eleven points. This uses no known Tits order formula,
minimal-index theorem or finite action catalogue. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleElevenPointTitsExclusion
open PrimitiveSocleRawStructure CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourAllParameterDerivedPositive CFSGReeFFourDerivedAmbientHom
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem binary_nine_dvd_order [Finite CFSG.Models.Tits] :
    512 ∣ Nat.card CFSG.Models.Tits := by
  letI : Finite (CFSGReeFFourFixedModelEquivalence.originalModelFixed 0) :=
    Finite.of_injective (CFSGReeFFourFixedAmbientHom.fixedAmbientHom 0)
      (CFSGReeFFourFixedAmbientHom.fixedAmbientHom_injective 0)
  have hp : IsPGroup 2 (derivedPositive 0) := by
    exact (positiveSylow 0).isPGroup'.of_equiv
      (MulEquiv.subgroupCongr (positiveSylow_coe 0))
  obtain ⟨a,ha⟩ := IsPGroup.iff_card.mp hp
  have hle : 2^9 ≤ 2^a := by
    simpa only [ha] using CFSGReeFFourDerivedPositiveCardLower.tits_positive_card_lower
  have h9 : 9 ≤ a := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hle
  have hpow : 512 ∣ Nat.card (derivedPositive 0) := by
    rw [ha]
    exact Nat.pow_dvd_pow 2 h9
  exact hpow.trans (Subgroup.card_dvd_of_injective titsPositiveHom titsPositiveHom_injective)

theorem degree_twelve_le_of_injective
    {X : Type} [Finite X] (f : CFSG.Models.Tits →* Equiv.Perm X)
    (hf : Function.Injective f) : 12 ≤ Nat.card X := by
  letI : Finite CFSG.Models.Tits :=
    Finite.of_injective f hf
  have hd : Nat.card CFSG.Models.Tits ∣ (Nat.card X).factorial := by
    simpa only [Nat.card_perm] using Subgroup.card_dvd_of_injective f hf
  by_contra hsmall
  have h512 : 512 ∣ Nat.factorial 11 :=
    binary_nine_dvd_order.trans (hd.trans (Nat.factorial_dvd_factorial (by omega)))
  exact (by decide : ¬ 512 ∣ Nat.factorial 11) h512

theorem simple_card_dvd_degree_factorial
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (D : NonaffineData G X) :
    Nat.card D.Simple ∣ (Nat.card X).factorial := by
  have hs : Nat.card (finiteGroupSocle G) = Nat.card D.Simple^D.factorCount := by
    rw [Nat.card_congr D.socleEquiv.toEquiv,Nat.card_fun,Nat.card_fin]
  have hdiv : Nat.card D.Simple ∣ Nat.card (finiteGroupSocle G) := by
    rw [hs]
    exact dvd_pow_self _ D.factorCount_pos.ne'
  have hG : Nat.card G ∣ (Nat.card X).factorial := by
    simpa only [Nat.card_perm] using Subgroup.card_dvd_of_injective
      (MulAction.toPermHom G X) MulAction.toPerm_injective
  exact hdiv.trans ((finiteGroupSocle G).card_subgroup_dvd_card.trans hG)

theorem not_tits_of_degree_le_eleven
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (D : NonaffineData G X) (hn : Nat.card X ≤ 11)
    (e : D.Simple ≃* CFSG.Models.Tits) : False := by
  letI : Finite CFSG.Models.Tits := Finite.of_equiv D.Simple e.toEquiv
  have hD := simple_card_dvd_degree_factorial D
  rw [Nat.card_congr e.toEquiv] at hD
  have h512 : 512 ∣ Nat.factorial 11 :=
    binary_nine_dvd_order.trans (hD.trans (Nat.factorial_dvd_factorial hn))
  exact (by decide : ¬ 512 ∣ Nat.factorial 11) h512

end SymmetricSubgroupAsymptotics.PrimitiveSocleElevenPointTitsExclusion
