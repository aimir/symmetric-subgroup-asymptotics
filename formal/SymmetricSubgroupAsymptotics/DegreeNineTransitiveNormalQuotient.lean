import SymmetricSubgroupAsymptotics.OrderNineAutomorphismDivisor
import SymmetricSubgroupAsymptotics.TransitiveAbelianNormalizerDivisor
import SymmetricSubgroupAsymptotics.SylowNormalizerImageLift
import SymmetricSubgroupAsymptotics.SylowPrimePowerTransitive
import SymmetricSubgroupAsymptotics.PrimitiveRelativeHeadOrderBudgets

/-! An actual transitive normal subgroup in a faithful nine-point action
cannot have quotient order nine. Frattini reduces that putative quotient to
the normalizer of its regular Sylow-three subgroup of order nine. The
normalizer order divides432, whereas the putative quotient forces81 to
divide it. No primitive or simple-group correspondence is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics

local instance degreeNinePrimeThreeFact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem ninePoint_normal_transitive_quotient_card_ne_nine
    {G : Type} [Group G] [Finite G] [MulAction G (Fin 9)]
    [FaithfulSMul G (Fin 9)] (S : Subgroup G) [S.Normal]
    [MulAction.IsPretransitive S (Fin 9)] : Nat.card (G ⧸ S) ≠ 9 := by
  intro hquot
  have hGdvd : Nat.card G ∣ 362880 := by
    have h := Subgroup.card_dvd_of_injective (MulAction.toPermHom G (Fin 9))
      (show Function.Injective (MulAction.toPermHom G (Fin 9)) from
        MulAction.toPerm_injective)
    simpa only [Nat.card_perm,Nat.card_fin] using h
  have hmS : Nat.card S * 9 = Nat.card G := by
    simpa only [Subgroup.index_eq_card,hquot] using S.card_mul_index
  have hSdvd : Nat.card S ∣ 40320 := by
    obtain ⟨k,hk⟩ := hGdvd
    refine ⟨k,?_⟩
    have hh := congrArg (fun n : ℕ => n*k) hmS
    nlinarith
  have hnine : 9 ∣ Nat.card S := by
    simpa only [Nat.card_fin] using degree_dvd_card_of_transitive_normal (X := Fin 9) S
  have hval : (Nat.card S).factorization 3 = 2 := by
    have hhi := (Nat.factorization_le_iff_dvd Nat.card_pos.ne'
      (by decide : 40320 ≠ 0)).mpr hSdvd 3
    have hlo : 2 ≤ (Nat.card S).factorization 3 :=
      (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hnine
    have hconst : (40320 : ℕ).factorization 3 = 2 := by decide +kernel
    rw [hconst] at hhi
    omega
  let P : Sylow 3 S := Classical.choice inferInstance
  have hP : Nat.card P = 9 := by rw [P.card_eq_multiplicity,hval]; decide
  letI : MulAction.IsPretransitive P (Fin 9) :=
    sylow_isPretransitive_of_card_eq_prime_pow (a := 2) P (by simp)
  let H : Subgroup G := (P : Subgroup S).map S.subtype
  have hHS : H ≤ S := by
    rintro _ ⟨x,hx,rfl⟩
    exact x.2
  have hH : Nat.card H = 9 := by
    dsimp only [H]
    rw [Subgroup.card_map_of_injective S.subtype_injective]
    exact hP
  letI : MulAction.IsPretransitive H (Fin 9) := ⟨fun x y => by
    obtain ⟨p,hp⟩ := MulAction.exists_smul_eq P x y
    exact ⟨⟨(p.1 : G),⟨p.1,p.2,rfl⟩⟩,hp⟩⟩
  have hcomm : IsMulCommutative H := IsMulCommutative.of_comm
    (IsPGroup.commutative_of_card_eq_prime_sq (p := 3) (by simpa using hH))
  let N := Subgroup.normalizer (H : Set G)
  have hNdvd : Nat.card N ∣ 432 := by
    have hn := normalizer_card_dvd_degree_mul_aut_of_abelian_transitive (X := Fin 9) H hcomm
    simp only [Nat.card_fin] at hn
    exact hn.trans (Nat.mul_dvd_mul_left 9
      (OrderNineAutomorphismDivisor.card_aut_dvd_fortyEight hH))
  let pi := QuotientGroup.mk' S
  have hS0 : S.map pi = ⊥ :=
    (Subgroup.map_eq_bot_iff S).mpr (QuotientGroup.ker_mk' S).ge
  have hH0 : H.map pi = ⊥ :=
    (Subgroup.map_eq_bot_iff H).mpr (hHS.trans (QuotientGroup.ker_mk' S).ge)
  have hsurj := SylowNormalizerImageLift.map_normalizer_eq_top pi
    (QuotientGroup.mk'_surjective S) S P (hS0.trans hH0.symm)
  let beta : N →* (G ⧸ S) := pi.comp N.subtype
  have hbeta : Function.Surjective beta := by
    intro q
    have hq : q ∈ N.map pi := by
      change q ∈ (Subgroup.normalizer (P.map S.subtype)).map pi
      rw [hsurj]
      trivial
    obtain ⟨x,hx,he⟩ := hq
    exact ⟨⟨x,hx⟩,he⟩
  let k : H →* beta.ker :=
    { toFun := fun x => ⟨⟨x.1,H.le_normalizer x.2⟩,by
        change pi x.1 = 1
        exact (QuotientGroup.eq_one_iff x.1).mpr (hHS x.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hk : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : beta.ker => (z.1.1 : G)) h
  have hker : 9 ∣ Nat.card beta.ker := by
    rw [←hH]
    exact Subgroup.card_dvd_of_injective k hk
  have hm := beta.ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr hbeta,Subgroup.card_top,hquot] at hm
  have h81 : 81 ∣ Nat.card N := by
    rw [←hm]
    exact Nat.mul_dvd_mul hker (dvd_refl 9)
  exact (by decide : ¬81 ∣ 432) (h81.trans hNdvd)

end SymmetricSubgroupAsymptotics
