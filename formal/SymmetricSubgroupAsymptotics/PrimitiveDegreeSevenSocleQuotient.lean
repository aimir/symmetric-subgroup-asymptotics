import SymmetricSubgroupAsymptotics.SevenPointSylowNormalizerBound
import SymmetricSubgroupAsymptotics.SylowNormalizerImageLift
import SymmetricSubgroupAsymptotics.PrimitiveRelativeHeadOrderBudgets
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart

/-! Frattini's argument bounds the actual quotient by a transitive normal
subgroup in a faithful seven-point action by six. In particular this
applies to the actual nonaffine full socle, without a primitive catalogue. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

local instance degreeSevenPrimeSevenFact : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem sevenPoint_normal_transitive_quotient_card_le_six
    {G : Type} [Group G] [Finite G] [MulAction G (Fin 7)]
    [FaithfulSMul G (Fin 7)] (S : Subgroup G) [S.Normal]
    [MulAction.IsPretransitive S (Fin 7)] : Nat.card (G ⧸ S) ≤ 6 := by
  have hd : Nat.card S ∣ 5040 := by
    have h := Subgroup.card_dvd_of_injective (MulAction.toPermHom S (Fin 7))
      (show Function.Injective (MulAction.toPermHom S (Fin 7)) from
        MulAction.toPerm_injective)
    simpa only [Nat.card_perm,Nat.card_fin] using h
  have hseven : 7 ∣ Nat.card S := by
    simpa only [Nat.card_fin] using
      degree_dvd_card_of_transitive_normal (X := Fin 7) S
  have hval : (Nat.card S).factorization 7 = 1 := by
    have hhi := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' (by decide : 5040 ≠ 0)).mpr hd 7
    have hlo := (Nat.Prime.dvd_iff_one_le_factorization (by decide : Nat.Prime 7)
      Nat.card_pos.ne').mp hseven
    have hconst : (5040 : ℕ).factorization 7 = 1 := by decide +kernel
    rw [hconst] at hhi
    omega
  let P : Sylow 7 S := Classical.choice inferInstance
  have hP : Nat.card P = 7 := by rw [P.card_eq_multiplicity,hval,pow_one]
  let H : Subgroup G := (P : Subgroup S).map S.subtype
  have hHS : H ≤ S := by
    rintro _ ⟨x,hx,rfl⟩
    exact x.2
  have hH : Nat.card H = 7 := by
    dsimp only [H]
    rw [Subgroup.card_map_of_injective S.subtype_injective]
    exact hP
  let pi := QuotientGroup.mk' S
  have hS0 : S.map pi = ⊥ := by
    apply (Subgroup.map_eq_bot_iff S).mpr
    exact (QuotientGroup.ker_mk' S).ge
  have hH0 : H.map pi = ⊥ := by
    apply (Subgroup.map_eq_bot_iff H).mpr
    exact hHS.trans (QuotientGroup.ker_mk' S).ge
  have hsurj := SylowNormalizerImageLift.map_normalizer_eq_top pi
    (QuotientGroup.mk'_surjective S) S P (hS0.trans hH0.symm)
  let N := Subgroup.normalizer (H : Set G)
  let beta : N →* (G ⧸ S) := pi.comp N.subtype
  have hbeta : Function.Surjective beta := by
    intro q
    have hq : q ∈ N.map pi := by
      change q ∈ (Subgroup.normalizer (P.map S.subtype)).map pi
      rw [hsurj]
      trivial
    obtain ⟨x,hx,he⟩ := hq
    exact ⟨⟨x,hx⟩,he⟩
  let k : H → beta.ker := fun x =>
    ⟨⟨x.1,H.le_normalizer x.2⟩,by
      change pi x.1 = 1
      exact (QuotientGroup.eq_one_iff x.1).mpr (hHS x.2)⟩
  have hk : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : beta.ker => (z.1.1 : G)) h
  have hker : 7 ≤ Nat.card beta.ker := by
    rw [←hH]
    exact Nat.card_le_card_of_injective k hk
  have hn : Nat.card N ≤ 42 := SevenPointSylowNormalizerBound.normalizer_card_le H hH
  have hm := beta.ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr hbeta,Subgroup.card_top] at hm
  have hmul := Nat.mul_le_mul_right (Nat.card (G ⧸ S)) hker
  nlinarith

namespace PrimitiveSocleRawStructure

theorem NonaffineData.degreeSeven_quotient_card_le_six
    {G : Type} [Group G] [Finite G] [MulAction G (Fin 7)]
    [FaithfulSMul G (Fin 7)] (D : NonaffineData G (Fin 7)) :
    Nat.card (G ⧸ finiteGroupSocle G) ≤ 6 := by
  letI : MulAction.IsPretransitive (finiteGroupSocle G) (Fin 7) := D.socle_transitive
  exact sevenPoint_normal_transitive_quotient_card_le_six (finiteGroupSocle G)

end PrimitiveSocleRawStructure
end SymmetricSubgroupAsymptotics
