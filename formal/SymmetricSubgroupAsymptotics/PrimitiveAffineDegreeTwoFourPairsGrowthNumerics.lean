import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourPairsGrowthPackage
import SymmetricSubgroupAsymptotics.CompleteCharacterIntervalTailBound

/-!
# Uniform raw numerics for the nonbinary four-pair rows

The degree-three affine prepend needs numerical facts about the literal
degree-eight pair package before it is pulled back to the signed quotient.
This file proves those facts uniformly over the ten published nonbinary
rows.  The constants are intentionally coarse, but are small enough for the
ambient width-twelve logarithmic-square menu.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

private abbrev NormalAxis8 (U : PreE7NonPairActionClass 8) :=
  {N : Subgroup (preE7NonPairAction 8 U) // N.Normal}

/-- Every literal width-eight action has order at most `2^16`. -/
theorem fourPairAction_card_le_two_pow_sixteen
    (U : PreE7NonPairActionClass 8) :
    Nat.card (preE7NonPairAction 8 U) ≤ 2 ^ 16 := by
  have h := Nat.card_le_card_of_injective
    (Subtype.val : preE7NonPairAction 8 U → Equiv.Perm (Fin 8))
    Subtype.val_injective
  rw [Nat.card_perm, Nat.card_fin] at h
  exact h.trans (by norm_num)

/-- The published permutation-generator theorem bounds the complete literal
normal menu of a width-eight action by `2^128`. -/
theorem fourPairAction_normalAxis_card_le
    (hgen : PermutationSubgroupGeneratorBound)
    (U : PreE7NonPairActionClass 8) :
    Nat.card (NormalAxis8 U) ≤ 2 ^ 128 := by
  simpa using CompleteCharacterIntervalData.normalAxis_card_le_two_pow_mul_width
    (U := preE7NonPairAction 8 U) hgen 16
      (fourPairAction_card_le_two_pow_sixteen U) (by norm_num)

private theorem fourPairAction_normalAxis_card_cast_le
    (hgen : PermutationSubgroupGeneratorBound)
    (U : PreE7NonPairActionClass 8) :
    (Nat.card (NormalAxis8 U) : ℝ) ≤ (2 : ℝ) ^ (128 : ℝ) := by
  have h := fourPairAction_normalAxis_card_le hgen U
  calc
    (Nat.card (NormalAxis8 U) : ℝ) ≤ ((2 ^ 128 : ℕ) : ℝ) := by
      exact_mod_cast h
    _ = (2 : ℝ) ^ (128 : ℝ) := by norm_num

private theorem s4_twice_aut_le_two_pow_144 :
    (2 : ℝ) * Nat.card (Equiv.Perm (Fin 4) ≃* Equiv.Perm (Fin 4)) ≤
      (2 : ℝ) ^ (144 : ℝ) := by
  let G := Equiv.Perm (Fin 4)
  have h : Nat.card (G ≃* G) ≤ 24 ^ 24 := by
    calc
      Nat.card (G ≃* G) ≤ Nat.card G ^ Nat.card G :=
        mulEquiv_card_le_card_pow_card G
      _ = 24 ^ 24 := by
        congr 1 <;> rw [Nat.card_perm, Nat.card_fin] <;> norm_num
  have hnat : 2 * Nat.card (G ≃* G) ≤ 2 ^ 144 :=
    (Nat.mul_le_mul_left 2 h).trans (by norm_num)
  exact_mod_cast hnat

private theorem one_le_one_add_natCast (b : ℕ) :
    (1 : ℝ) ≤ 1 + (b : ℝ) := by
  have hb : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  linarith

private theorem normalModel_rawMain_le
    {U : PreE7NonPairActionClass 8}
    (M : PreE7NormalComparatorModel 8 U) :
    M.toData.rawMainCoefficient ≤ Nat.card (NormalAxis8 U) := by
  have h := M.main_total_le_card .lin 0
  simpa only [PreE7SmallAdditiveData.rawMainCoefficient,
    fusionAxisEnvelopeTotal, PreE7SmallAdditiveData.certificate] using h

private theorem normalModel_rawTail_eq
    {U : PreE7NonPairActionClass 8}
    (M : PreE7NormalComparatorModel 8 U) :
    M.toData.rawTailCoefficient = M.tailConstant := by
  have h := M.tail_total_eq .lin 0
  simpa only [PreE7SmallAdditiveData.rawTailCoefficient,
    fusionAxisEnvelopeTotal, PreE7SmallAdditiveData.certificate] using h

private theorem factorModel_rawMain_le
    {U : PreE7NonPairActionClass 8}
    (M : PreE7FactorComparatorModel 8 U) :
    M.toData.rawMainCoefficient ≤
      Nat.card (NormalAxis8 U) + M.mainConstant := by
  have h := M.main_total_le_card_add .lin 0
  simpa only [PreE7SmallAdditiveData.rawMainCoefficient,
    fusionAxisEnvelopeTotal, PreE7SmallAdditiveData.certificate] using h

private theorem factorModel_rawTail_eq
    {U : PreE7NonPairActionClass 8}
    (M : PreE7FactorComparatorModel 8 U) :
    M.toData.rawTailCoefficient = M.tailConstant := by
  have h := M.tail_total_eq .lin 0
  simpa only [PreE7SmallAdditiveData.rawTailCoefficient,
    fusionAxisEnvelopeTotal, PreE7SmallAdditiveData.certificate] using h

private theorem easy_small_main_le
    (hgen : PermutationSubgroupGeneratorBound)
    (lit : PreE7CharacterLiterature)
    {U : PreE7NonPairActionClass 8}
    (M : CertifiedFourPairEasyModel U)
    (hsmall : ∀ S : PreE7Y1SourceData 8 U,
      M ≠ .repeatedNaturalA4 S) :
    (M.quotientSummedEnvelope lit).mainCoefficient ≤
      (2 : ℝ) ^ (320 : ℝ) := by
  cases M with
  | linear S =>
      cases S with
      | gl e h =>
          let D := linGLModel U e h
          have hm := normalModel_rawMain_le D
          have ha := fourPairAction_normalAxis_card_cast_le hgen U
          change D.toData.rawMainCoefficient ≤ _
          exact hm.trans (ha.trans (Real.rpow_le_rpow_of_exponent_le
            (by norm_num) (by norm_num)))
      | sl e h =>
          let D := linSLModel U e h
          have hm := factorModel_rawMain_le D
          have ha := fourPairAction_normalAxis_card_cast_le hgen U
          change D.toData.rawMainCoefficient ≤ _
          have hmain : D.mainConstant = 1 := rfl
          rw [hmain] at hm
          calc
            D.toData.rawMainCoefficient ≤
                (Nat.card (NormalAxis8 U) : ℝ) + 1 := hm
            _ ≤ (2 : ℝ) ^ (128 : ℝ) + 1 := by linarith
            _ ≤ (2 : ℝ) ^ (129 : ℝ) := by norm_num
            _ ≤ (2 : ℝ) ^ (320 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  | abstractSymmetricFour e =>
      let D := CertifiedFourPairEasyModel.abstractS4Model e
      have hm := normalModel_rawMain_le D
      have ha := fourPairAction_normalAxis_card_cast_le hgen U
      change D.toData.rawMainCoefficient ≤ _
      exact hm.trans (ha.trans (Real.rpow_le_rpow_of_exponent_le
        (by norm_num) (by norm_num)))
  | repeatedNaturalA4 S => exact False.elim (hsmall S rfl)

private theorem easy_small_cold_le
    (lit : PreE7CharacterLiterature)
    {U : PreE7NonPairActionClass 8}
    (M : CertifiedFourPairEasyModel U)
    (hsmall : ∀ S : PreE7Y1SourceData 8 U,
      M ≠ .repeatedNaturalA4 S) :
    ∀ b, (M.quotientSummedEnvelope lit).coldCoefficient b ≤
      (2 : ℝ) ^ (320 : ℝ) * (1 + b) := by
  intro b
  have hb1 : (1 : ℝ) ≤ 1 + (b : ℝ) := one_le_one_add_natCast b
  cases M with
  | linear S =>
      cases S with
      | gl e h =>
          let D := linGLModel U e h
          have ht' := normalModel_rawTail_eq D
          change D.toData.rawTailCoefficient ≤ _
          rw [ht']
          change (2 : ℝ) * Nat.card (Equiv.Perm (Fin 4) ≃*
            Equiv.Perm (Fin 4)) ≤ _
          exact (s4_twice_aut_le_two_pow_144.trans
            (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))).trans
              (le_mul_of_one_le_right (by positivity) hb1)
      | sl e h =>
          let D := linSLModel U e h
          have ht := factorModel_rawTail_eq D
          change D.toData.rawTailCoefficient ≤ _
          rw [ht]
          change (0 : ℝ) ≤ _
          positivity
  | abstractSymmetricFour e =>
      let D := CertifiedFourPairEasyModel.abstractS4Model e
      have ht := normalModel_rawTail_eq D
      change D.toData.rawTailCoefficient ≤ _
      rw [ht]
      change (2 : ℝ) * Nat.card (Equiv.Perm (Fin 4) ≃*
        Equiv.Perm (Fin 4)) ≤ _
      exact (s4_twice_aut_le_two_pow_144.trans
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))).trans
          (le_mul_of_one_le_right (by positivity) hb1)
  | repeatedNaturalA4 S => exact False.elim (hsmall S rfl)

/-- The fixed Y1 quotient constants are bounded from its literal order and
the published permutation-generator theorem. -/
theorem y1_rawConstant_le_two_pow_208
    (hgen : PermutationSubgroupGeneratorBound)
    {U : PreE7NonPairActionClass 8}
    (S : PreE7Y1SourceData 8 U) :
    S.constant ≤ (2 : ℝ) ^ (208 : ℝ) := by
  let A := preE7NonPairAction 8 U
  have horder : Nat.card A ≤ 2 ^ 16 :=
    fourPairAction_card_le_two_pow_sixteen U
  have haxes := fourPairAction_normalAxis_card_cast_le hgen U
  have hterm : ∀ N : NormalAxis8 U,
      (S.quotient N).constant ≤ (2 : ℝ) ^ (80 : ℝ) := by
    intro N
    letI : N.1.Normal := N.2
    have hquot : Nat.card (A ⧸ N.1) ≤ 2 ^ 16 :=
      (Nat.card_le_card_of_surjective (QuotientGroup.mk' N.1)
        (QuotientGroup.mk'_surjective N.1)).trans horder
    cases hcert : S.quotient N with
    | character c hslope =>
        change (Nat.card ((A ⧸ N.1) ≃* (A ⧸ N.1)) : ℝ) ≤ _
        have h :=
          CompleteCharacterIntervalData.quotient_mulEquiv_card_le_two_pow_generator
            (U := A) hgen 16 horder N.1
        norm_num at h ⊢
        exact_mod_cast h
    | headed H hweight =>
        change (Nat.card (A ⧸ N.1) : ℝ) ≤ _
        calc
          (Nat.card (A ⧸ N.1) : ℝ) ≤ ((2 ^ 16 : ℕ) : ℝ) := by
            exact_mod_cast hquot
          _ = (2 : ℝ) ^ (16 : ℝ) := by norm_num
          _ ≤ (2 : ℝ) ^ (80 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  letI : Fintype (NormalAxis8 U) := Subtype.fintype Subgroup.Normal
  unfold PreE7Y1ActionCertificate.constant
  calc
    _ ≤ ∑ _N : NormalAxis8 U, (2 : ℝ) ^ (80 : ℝ) :=
      Finset.sum_le_sum (fun N _ => hterm N)
    _ = (Nat.card (NormalAxis8 U) : ℝ) * (2 : ℝ) ^ (80 : ℝ) := by
      simp [Nat.card_eq_fintype_card, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ (128 : ℝ) * (2 : ℝ) ^ (80 : ℝ) :=
      mul_le_mul_of_nonneg_right haxes (by positivity)
    _ = (2 : ℝ) ^ (208 : ℝ) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      norm_num

private theorem central_lowerConstant_le_two_pow_144
    {U : PreE7NonPairActionClass 8}
    (M : PublishedFourPairCentralModel U) :
    M.literalData.lowerConstant ≤ (2 : ℝ) ^ (144 : ℝ) := by
  cases M with
  | alternatingFourTimesTwo e =>
      change (156 : ℝ) ≤ _
      norm_num
  | symmetricFourTimesTwo e =>
      change CentralBinaryProductModels.s4ColdConstant ≤ _
      exact s4_twice_aut_le_two_pow_144

private theorem central_main_le
    (hgen : PermutationSubgroupGeneratorBound)
    {U : PreE7NonPairActionClass 8}
    (M : PublishedFourPairCentralModel U) :
    M.literalData.normalCount ≤ (2 : ℝ) ^ (320 : ℝ) := by
  change (Nat.card (NormalAxis8 U) : ℝ) ≤ _
  exact (fourPairAction_normalAxis_card_cast_le hgen U).trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))

private theorem central_cold_le
    (hgen : PermutationSubgroupGeneratorBound)
    {U : PreE7NonPairActionClass 8}
    (M : PublishedFourPairCentralModel U) (b : ℕ) :
    M.literalData.normalCount * M.literalData.lowerConstant ≤
      (2 : ℝ) ^ (320 : ℝ) * (1 + b) := by
  have ha := fourPairAction_normalAxis_card_cast_le hgen U
  have hl := central_lowerConstant_le_two_pow_144 M
  have hprod := mul_le_mul ha hl M.literalData.lowerConstant_nonneg
    (by positivity : 0 ≤ (2 : ℝ) ^ (128 : ℝ))
  calc
    M.literalData.normalCount * M.literalData.lowerConstant ≤
        (2 : ℝ) ^ (128 : ℝ) * (2 : ℝ) ^ (144 : ℝ) := hprod
    _ = (2 : ℝ) ^ (272 : ℝ) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      norm_num
    _ ≤ (2 : ℝ) ^ (320 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ ≤ (2 : ℝ) ^ (320 : ℝ) * (1 + b) := by
      nth_rewrite 1 [← mul_one ((2 : ℝ) ^ (320 : ℝ))]
      exact mul_le_mul_of_nonneg_left
        (one_le_one_add_natCast b) (by positivity)

private theorem character_tail_le_two_pow_208
    (hgen : PermutationSubgroupGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    {U : PreE7NonPairActionClass 8}
    (M : CertifiedFourPairCharacterModel U) :
    (M.completeInterval hZmud).tailConstant ≤
      (2 : ℝ) ^ (208 : ℝ) := by
  have h :=
    CompleteCharacterIntervalData.tailConstant_le_two_pow_of_order_and_generators
      (M.completeInterval hZmud) hgen 16
      (fourPairAction_card_le_two_pow_sixteen U) (by norm_num)
  norm_num at h ⊢
  exact h

private theorem logb_two_five_div_three_lt_seven_ninths :
    Real.logb 2 5 / 3 < (7 : ℝ) / 9 := by
  have hp : (5 : ℝ) ^ (3 : ℕ) < (2 : ℝ) ^ (7 : ℕ) := by norm_num
  have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (5 : ℝ) ^ (3 : ℕ)) hp
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlog
  have hscaled : 3 * Real.logb 2 5 < (7 : ℝ) := by
    simpa only [mul_comm] using hlog
  calc
    Real.logb 2 5 / 3 = (3 * Real.logb 2 5) / 9 := by ring
    _ < 7 / 9 := by nlinarith

/-- Uniform numerical information retained by every published nonbinary
four-pair growth row. -/
structure FourPairGrowthNumerics
    {Q : Type} [Group Q] [Finite Q]
    (G : PreE7DegreeTwoPairQuotientSummedPackage Q) : Prop where
  degree_two_le : 2 ≤ G.v
  degree_le_six : G.v ≤ 6
  eta_eq_zero : G.envelope.eta = 0
  theta_le : G.envelope.theta ≤ 7 / 9
  main_le : ∀ b : ℕ, G.envelope.mainCoefficient ≤
    (2 : ℝ) ^ (320 : ℝ) * (1 + b)
  cold_le : ∀ b, G.envelope.coldCoefficient b ≤
    (2 : ℝ) ^ (320 : ℝ) * (1 + b)

namespace FourPairGrowthNumerics

/-- Literal target transport preserves every scalar in the retained row. -/
noncomputable def comapEquiv
    {Q Q' : Type} [Group Q] [Finite Q] [Group Q'] [Finite Q']
    (e : Q ≃* Q')
    (G : PreE7DegreeTwoPairQuotientSummedPackage Q')
    (N : FourPairGrowthNumerics G) :
    FourPairGrowthNumerics (G.comapEquiv e) := by
  exact
    { degree_two_le := N.degree_two_le
      degree_le_six := N.degree_le_six
      eta_eq_zero := N.eta_eq_zero
      theta_le := N.theta_le
      main_le := N.main_le
      cold_le := N.cold_le }

end FourPairGrowthNumerics

namespace PublishedDegreeTwoFourPairRow

private theorem linear_ne_repeated
    {U : PreE7NonPairActionClass 8}
    (S : PreE7LinSource 8 U) (T : PreE7Y1SourceData 8 U) :
    (CertifiedFourPairEasyModel.linear S : CertifiedFourPairEasyModel U) ≠
      .repeatedNaturalA4 T := by
  simp

private theorem abstractS4_ne_repeated
    {U : PreE7NonPairActionClass 8}
    (e : preE7NonPairAction 8 U ≃* Equiv.Perm (Fin 4))
    (T : PreE7Y1SourceData 8 U) :
    (CertifiedFourPairEasyModel.abstractSymmetricFour e :
      CertifiedFourPairEasyModel U) ≠ .repeatedNaturalA4 T := by
  simp

private structure RawGrowthNumerics
    (v : ℕ) (eta theta main : ℝ) (cold : ℕ → ℝ) : Prop where
  degree_two_le : 2 ≤ v
  degree_le_six : v ≤ 6
  eta_eq_zero : eta = 0
  theta_le : theta ≤ 7 / 9
  main_le : ∀ b : ℕ, main ≤ (2 : ℝ) ^ (320 : ℝ) * (1 + b)
  cold_le : ∀ b : ℕ, cold b ≤ (2 : ℝ) ^ (320 : ℝ) * (1 + b)

private noncomputable def RawGrowthNumerics.toGrowth
    {Q : Type} [Group Q] [Finite Q]
    (G : PreE7DegreeTwoPairQuotientSummedPackage Q)
    {v : ℕ} {eta theta main : ℝ} {cold : ℕ → ℝ}
    (N : RawGrowthNumerics v eta theta main cold)
    (hv : G.v = v)
    (heta : G.envelope.eta = eta)
    (htheta : G.envelope.theta = theta)
    (hmain : G.envelope.mainCoefficient = main)
    (hcold : G.envelope.coldCoefficient = cold) :
    FourPairGrowthNumerics G := by
  refine
    { degree_two_le := by rw [hv]; exact N.degree_two_le
      degree_le_six := by rw [hv]; exact N.degree_le_six
      eta_eq_zero := by rw [heta]; exact N.eta_eq_zero
      theta_le := by rw [htheta]; exact N.theta_le
      main_le := fun b => by rw [hmain]; exact N.main_le b
      cold_le := fun b => by rw [hcold]; exact N.cold_le b }

private noncomputable def rawGrowthNumerics_sl
    (hgen : PermutationSubgroupGeneratorBound)
    {U : PreE7NonPairActionClass 8}
    (e : LinearThree.NV ≃ Fin 8)
    (h : preE7NonPairAction 8 U = relabelSubgroup e
      (LinearThree.natural.comp LinearThree.slSub.subtype).range) :
    let D := (linSLModel U e h).toData
    RawGrowthNumerics D.degree 0 D.tailSlope D.rawMainCoefficient
      (fun _ => D.rawTailCoefficient) := by
  let D := (linSLModel U e h).toData
  refine
    { degree_two_le := by
        change 2 ≤ D.degree
        norm_num [D, PreE7FactorComparatorModel.toData, linSLModel]
      degree_le_six := by
        change D.degree ≤ 6
        norm_num [D, PreE7FactorComparatorModel.toData, linSLModel]
      eta_eq_zero := rfl
      theta_le := by
        change D.tailSlope ≤ 7 / 9
        norm_num [D, PreE7FactorComparatorModel.toData, linSLModel]
      main_le := fun b => by
        have hm := factorModel_rawMain_le (linSLModel U e h)
        have ha := fourPairAction_normalAxis_card_cast_le hgen U
        change D.rawMainCoefficient ≤ _
        have hmain : (linSLModel U e h).mainConstant = 1 := rfl
        rw [hmain] at hm
        calc
          D.rawMainCoefficient ≤
              (Nat.card (NormalAxis8 U) : ℝ) + 1 := hm
          _ ≤ (2 : ℝ) ^ (128 : ℝ) + 1 := by linarith
          _ ≤ (2 : ℝ) ^ (129 : ℝ) := by norm_num
          _ ≤ (2 : ℝ) ^ (320 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ ≤ (2 : ℝ) ^ (320 : ℝ) * (1 + b) := by
            nth_rewrite 1 [← mul_one ((2 : ℝ) ^ (320 : ℝ))]
            exact mul_le_mul_of_nonneg_left (one_le_one_add_natCast b)
              (by positivity)
      cold_le := fun b => by
        have ht := factorModel_rawTail_eq (linSLModel U e h)
        change D.rawTailCoefficient ≤ _
        rw [ht]
        change (0 : ℝ) ≤ _
        positivity }

private noncomputable def rawGrowthNumerics_y1
    (hgen : PermutationSubgroupGeneratorBound)
    {U : PreE7NonPairActionClass 8}
    (S : PreE7Y1SourceData 8 U) :
    RawGrowthNumerics 2 0 (153 / 200) 0
      (fun b => S.constant * (1 + b)) := by
  refine
    { degree_two_le := by norm_num
      degree_le_six := by norm_num
      eta_eq_zero := rfl
      theta_le := by norm_num
      main_le := fun _ => by positivity
      cold_le := fun b => by
        exact mul_le_mul_of_nonneg_right
          ((y1_rawConstant_le_two_pow_208 hgen S).trans
            (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)))
          (by positivity) }

private noncomputable def rawGrowthNumerics_central
    (hgen : PermutationSubgroupGeneratorBound)
    {U : PreE7NonPairActionClass 8}
    (M : PublishedFourPairCentralModel U) :
    RawGrowthNumerics 5 0 (3 / 5) M.literalData.normalCount
      (fun _ => M.literalData.normalCount * M.literalData.lowerConstant) := by
  refine
    { degree_two_le := by norm_num
      degree_le_six := by norm_num
      eta_eq_zero := rfl
      theta_le := by norm_num
      main_le := fun b => (central_main_le hgen M).trans (by
        nth_rewrite 1 [← mul_one ((2 : ℝ) ^ (320 : ℝ))]
        exact mul_le_mul_of_nonneg_left (one_le_one_add_natCast b)
          (by positivity))
      cold_le := central_cold_le hgen M }

private noncomputable def rawGrowthNumerics_character
    (hgen : PermutationSubgroupGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    {U : PreE7NonPairActionClass 8}
    (M : CertifiedFourPairCharacterModel U) :
    RawGrowthNumerics
      (max 2 (M.completeInterval hZmud).quotientDegree) 0
      ((M.interval.slots : ℝ) * (Real.logb 2 5 / 3)) 1
      (fun _ => (M.completeInterval hZmud).tailConstant) := by
  refine
    { degree_two_le := by
        exact le_max_left _ _
      degree_le_six := by
        apply max_le (by norm_num)
        simpa only [CertifiedFourPairCharacterModel.completeInterval,
          SocleGeneratorCharacterIntervalData.toCompleteCharacterIntervalData_quotientDegree]
          using M.quotientDegree_le_six
      eta_eq_zero := rfl
      theta_le := by
        rw [M.slots_eq_one]
        norm_num only [Nat.cast_one, one_mul]
        exact logb_two_five_div_three_lt_seven_ninths.le
      main_le := fun b => by
        calc
          (1 : ℝ) ≤ (2 : ℝ) ^ (320 : ℝ) :=
            Real.one_le_rpow (by norm_num) (by norm_num)
          _ = (2 : ℝ) ^ (320 : ℝ) * 1 := by ring
          _ ≤ (2 : ℝ) ^ (320 : ℝ) * (1 + b) :=
            mul_le_mul_of_nonneg_left (one_le_one_add_natCast b) (by positivity)
      cold_le := fun b => by
        have h208 : (2 : ℝ) ^ (208 : ℝ) ≤ (2 : ℝ) ^ (320 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        exact (character_tail_le_two_pow_208 hgen hZmud M).trans
          (h208.trans (by
            nth_rewrite 1 [← mul_one ((2 : ℝ) ^ (320 : ℝ))]
            exact mul_le_mul_of_nonneg_left (one_le_one_add_natCast b)
              (by positivity))) }

/-- The ten classified nonbinary rows share one degree, slope and
coefficient envelope before affine prepending. -/
noncomputable def growthNumerics
    (hgen : PermutationSubgroupGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {U : PreE7NonPairActionClass 8}
    (M : PublishedDegreeTwoFourPairRow U) :
    FourPairGrowthNumerics (M.quotientSummedPackage hZmud lit) := by
  cases M with
  | easy M =>
      cases M with
      | linear S =>
          cases S with
          | gl e h =>
              have hsmall : ∀ S : PreE7Y1SourceData 8 U,
                  (CertifiedFourPairEasyModel.linear (.gl e h) :
                    CertifiedFourPairEasyModel U) ≠ .repeatedNaturalA4 S :=
                fun S => linear_ne_repeated (.gl e h) S
              let M : CertifiedFourPairEasyModel U := .linear (.gl e h)
              change FourPairGrowthNumerics (M.quotientSummedPackage lit)
              refine
                { degree_two_le := by
                    change 2 ≤ (4 : ℕ)
                    norm_num
                  degree_le_six := by
                    change (4 : ℕ) ≤ 6
                    norm_num
                  eta_eq_zero := rfl
                  theta_le := by
                    change (3 / 4 : ℝ) ≤ 7 / 9
                    norm_num
                  main_le := fun b =>
                    (easy_small_main_le hgen lit M hsmall).trans (by
                      nth_rewrite 1 [← mul_one ((2 : ℝ) ^ (320 : ℝ))]
                      exact mul_le_mul_of_nonneg_left
                        (one_le_one_add_natCast b) (by positivity))
                  cold_le := easy_small_cold_le lit M hsmall }
          | sl e h =>
              apply RawGrowthNumerics.toGrowth _
                (rawGrowthNumerics_sl hgen e h)
              all_goals rfl
      | abstractSymmetricFour e =>
          have hsmall : ∀ S : PreE7Y1SourceData 8 U,
              (CertifiedFourPairEasyModel.abstractSymmetricFour e :
                CertifiedFourPairEasyModel U) ≠ .repeatedNaturalA4 S :=
            fun S => abstractS4_ne_repeated e S
          let M : CertifiedFourPairEasyModel U := .abstractSymmetricFour e
          change FourPairGrowthNumerics (M.quotientSummedPackage lit)
          refine
            { degree_two_le := by
                change 2 ≤ (3 : ℕ)
                norm_num
              degree_le_six := by
                change (3 : ℕ) ≤ 6
                norm_num
              eta_eq_zero := rfl
              theta_le := by
                change (1 / 4 : ℝ) ≤ 7 / 9
                norm_num
              main_le := fun b =>
                (easy_small_main_le hgen lit M hsmall).trans (by
                  nth_rewrite 1 [← mul_one ((2 : ℝ) ^ (320 : ℝ))]
                  exact mul_le_mul_of_nonneg_left
                    (one_le_one_add_natCast b) (by positivity))
              cold_le := easy_small_cold_le lit M hsmall }
      | repeatedNaturalA4 S =>
          apply RawGrowthNumerics.toGrowth _
            (rawGrowthNumerics_y1 hgen S)
          all_goals rfl
  | central M =>
      apply RawGrowthNumerics.toGrowth _
        (rawGrowthNumerics_central hgen M)
      all_goals rfl
  | character M =>
      apply RawGrowthNumerics.toGrowth _
        (rawGrowthNumerics_character hgen hZmud M)
      all_goals rfl

end PublishedDegreeTwoFourPairRow

/-- The selected catalogue representative retains the same uniform
numerics as its certified row. -/
noncomputable def degreeTwoFourPairRepresentativeGrowthNumerics
    (hgen : PermutationSubgroupGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (published : PublishedDegreeTwoFourPairClassification)
    (p : PreE7PairActionClass 4) :
    FourPairGrowthNumerics
      (degreeTwoFourPairRepresentativePackage hZmud lit published p) := by
  simpa only [degreeTwoFourPairRepresentativePackage] using
    (Classical.choice (published p)).growthNumerics hgen hZmud lit

/-- Uniform numerics on the actual nonbinary four-pair action. -/
noncomputable def degreeTwoFourPairLiteralGrowthNumerics
    (hgen : PermutationSubgroupGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (published : PublishedDegreeTwoFourPairClassification)
    (A : Subgroup (Equiv.Perm (Fin 8)))
    (hA : ¬ IsPGroup 2 A)
    (htrans : MulAction.IsPretransitive A (Fin 8))
    (F : BinaryPairFrame A (Fin 4)) :
    FourPairGrowthNumerics
      (degreeTwoFourPairLiteralPackage hZmud lit published
        A hA htrans F) := by
  let C := fourPairRepresentativeChart A hA htrans F
  exact FourPairGrowthNumerics.comapEquiv C.sourceEquiv
    (degreeTwoFourPairRepresentativePackage hZmud lit published
      C.representative)
    (degreeTwoFourPairRepresentativeGrowthNumerics hgen hZmud lit published
      C.representative)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
