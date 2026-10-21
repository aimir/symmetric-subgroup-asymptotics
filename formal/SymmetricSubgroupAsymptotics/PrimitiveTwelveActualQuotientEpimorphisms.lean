import SymmetricSubgroupAsymptotics.OrderTenEpimorphismGeneratorEnvelope
import SymmetricSubgroupAsymptotics.PrimitiveSmallSocleSingleFactor
import SymmetricSubgroupAsymptotics.PrimitiveOuterOrderRoundingGap
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawOneFactor
import SymmetricSubgroupAsymptotics.MonolithicSocleOne
import SymmetricSubgroupAsymptotics.SocleNormalGeneratorNumber
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixTailSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallNumerics

/-! All actual normal quotients of a nonaffine primitive twelve-point
group admit slope5/3. The zero axis uses the one simple full-socle factor;
every nonzero original normal contains it and has quotient order at most
ten. This is a consumer estimate, not a degree-twelve group locator or an
assertion that all its normals are normally cyclic. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

variable {G : Type} [Group G] [Finite G] [MulAction G (Fin 12)]
    [FaithfulSMul G (Fin 12)]

omit [FaithfulSMul G (Fin 12)] in
theorem NonaffineData.degreeTwelve_quotient_card_le_ten
    (D : NonaffineData G (Fin 12)) (hindex : PublishedSimpleIndexBounds) :
    Nat.card (G ⧸ finiteGroupSocle G) ≤ 10 := by
  have hk := D.factorCount_one_of_degree_lt_twentyFive hindex (by simp)
  obtain ⟨ell,_,hf,he,hlog⟩ := D.oneFactor_quotient_log_bound hk hindex
  have hpow := quotientOrder_twoPow_le_cube_of_log (by omega) hlog
  have he' : ell ≤ 12 := by simpa only [Nat.card_fin] using he
  have hcube : 2 ^ Nat.card (G ⧸ finiteGroupSocle G) ≤ 1728 :=
    hpow.trans (Nat.pow_le_pow_left he' 3)
  by_contra h
  have hlo : 11 ≤ Nat.card (G ⧸ finiteGroupSocle G) := by omega
  have hbad : 2048 ≤ 1728 := calc
    2048 = 2 ^ 11 := by decide
    _ ≤ 2 ^ Nat.card (G ⧸ finiteGroupSocle G) :=
      pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hlo
    _ ≤ 1728 := hcube
  omega

omit [FaithfulSMul G (Fin 12)] in
theorem NonaffineData.degreeTwelve_socle_one
    (D : NonaffineData G (Fin 12)) (hindex : PublishedSimpleIndexBounds) :
    SocleNormalGeneratorBound G 1 := by
  have hk := D.factorCount_one_of_degree_lt_twentyFive hindex (by simp)
  apply (socleNormalGeneratorBound_iff_normalGen_le G 1).mpr
  exact MonolithicSocleOne.normalGen_le_one (finiteGroupSocle G)
    (D.oneFactor_socle_nontrivial hk)
    (fun N _ hN => D.oneFactor_socle_le hk N inferInstance hN)

omit [FaithfulSMul G (Fin 12)] in
theorem NonaffineData.degreeTwelve_nonzero_normal_quotient_card_le_ten
    (D : NonaffineData G (Fin 12)) (hindex : PublishedSimpleIndexBounds)
    (M : Subgroup G) [M.Normal] (hM : M ≠ ⊥) : Nat.card (G ⧸ M) ≤ 10 := by
  have hk := D.factorCount_one_of_degree_lt_twentyFive hindex (by simp)
  have hSM := D.oneFactor_socle_le hk M inferInstance hM
  let f : (G ⧸ finiteGroupSocle G) →* (G ⧸ M) :=
    QuotientGroup.lift (finiteGroupSocle G) (QuotientGroup.mk' M) (by
      simpa only [QuotientGroup.ker_mk'] using hSM)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective M q
    exact ⟨((g : G) : G ⧸ finiteGroupSocle G),rfl⟩
  exact (Nat.card_le_card_of_surjective f hf).trans (D.degreeTwelve_quotient_card_le_ten hindex)

omit [Finite G] in
theorem degreeTwelve_group_order_le : Nat.card G ≤ 2^29 := by
  have h := Nat.card_le_card_of_injective (MulAction.toPermHom G (Fin 12))
    (show Function.Injective (MulAction.toPermHom G (Fin 12)) from MulAction.toPerm_injective)
  rw [Nat.card_perm,Nat.card_fin] at h
  exact h.trans (by decide)

theorem NonaffineData.degreeTwelve_actual_normal_quotient_epi_le
    (D : NonaffineData G (Fin 12)) (hindex : PublishedSimpleIndexBounds)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (hMN : PermutationSubgroupGeneratorBound)
    (M : Subgroup G) [M.Normal] (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (G ⧸ M)) : ℝ) ≤
      (2 : ℝ)^(841 : ℕ) * (2 : ℝ)^((5/3 : ℝ)*(b : ℝ)) := by
  by_cases hM : M = ⊥
  · subst M
    have he := (hZmud.generalCertificate (D.degreeTwelve_socle_one hindex)).envelope lit b J
    simp only [ZmudFaithfulCharacterTupleInput.generalCertificate_slope,
      Nat.cast_one,one_mul] at he
    have haut : (Nat.card (G ≃* G) : ℝ) ≤ (2 : ℝ)^(841 : ℕ) := by
      have hn := mulEquiv_card_le_two_pow_sq_of_order 29
        (degreeTwelve_group_order_le (G := G))
      exact_mod_cast hn
    have hlog : Real.logb 2 5/3 ≤ (5/3 : ℝ) := by
      have h := logb_two_five_div_five_lt_seven_fifteenths
      linarith
    have hp : (2 : ℝ)^((Real.logb 2 5/3)*(b : ℝ)) ≤
        (2 : ℝ)^((5/3 : ℝ)*(b : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg b))
    have hcard := fusionGroupEpimorphism_card_congr (MulEquiv.refl J)
      (QuotientGroup.quotientBot : G ⧸ (⊥ : Subgroup G) ≃* G)
    rw [hcard]
    exact he.trans (mul_le_mul haut hp (by positivity) (by positivity))
  · have hs := epimorphism_card_le_ten_of_order_le_ten
      (D.degreeTwelve_nonzero_normal_quotient_card_le_ten hindex M hM) hMN b J
    exact hs.trans (mul_le_mul_of_nonneg_right
      (show (10 : ℝ) ≤ (2 : ℝ)^(841 : ℕ) from
        (by norm_num : (10 : ℝ) ≤ (2 : ℝ)^(4 : ℕ)).trans
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by decide : 4 ≤ 841))) (by positivity))

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
