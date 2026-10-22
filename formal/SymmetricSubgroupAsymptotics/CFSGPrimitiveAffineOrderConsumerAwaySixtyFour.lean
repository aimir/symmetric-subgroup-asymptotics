import SymmetricSubgroupAsymptotics.PrimitiveAffineActualFiniteDataConstruction
import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineOrderTraceSources
import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineBinaryFiveSource
import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineEightyOneOrderSource

/-! Actual primitive-affine sources away from degree64, using only proved
finite25/5 facts and original order/trace estimates. No primitive composition
length hypothesis, or stronger degree81 soluble-complement order theorem,
is requested. Degree64 remains an explicit excluded degree here. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
namespace CFSGPrimitiveAffineOrderConsumer

private def degree25Data : PublishedDegreeTwentyFiveLinearData :=
  DegreeTwentyFiveActualProjectiveData.publishedDegreeTwentyFiveLinearData
    burnsideTwoPrimeSolvability PGLTwoFiveIsomorphism.publishedProjectiveIsomorphism

private def solubleCentral : PublishedSolublePrimitiveAffineSmallCentralInput where
  degreeTwentyFiveProjectiveDatum := degree25Data.solubleProjective

private theorem window27 :
    PrimitiveAffineSolubleOddOrderSource.tailSlope 78 ≤
      preE7CharacterWindow 27 := by
  have hp : ((78 : ℝ) ^ 10) < (2 : ℝ) ^ (63 : ℕ) := by norm_num
  have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by norm_num) 10) hp
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hl
  unfold PrimitiveAffineSolubleOddOrderSource.tailSlope
    preE7CharacterWindow preE7CharacterRho halfDegree
  norm_num at hl ⊢
  linarith

private theorem window49 :
    PrimitiveAffineSolubleOddOrderSource.tailSlope (49 ^ 2) ≤
      preE7CharacterWindow 49 := by
  have hp : ((7 : ℝ) ^ (16 : ℕ)) < (2 : ℝ) ^ (45 : ℕ) := by norm_num
  have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by norm_num) 16) hp
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hl
  unfold PrimitiveAffineSolubleOddOrderSource.tailSlope
    preE7CharacterWindow preE7CharacterRho halfDegree
  have hq : (((49 ^ 2 : ℕ) : ℝ)) = (7 : ℝ) ^ (4 : ℕ) := by norm_num
  rw [hq, Real.logb_pow]
  norm_num at hl ⊢
  linarith

private noncomputable def solubleSource27
    (hgen : PermutationSubgroupGeneratorBound)
    (U : PreE7NonPairActionClass 27)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 27 U) (Fin 27))
    (P : PrimitiveAffineProfile (preE7NonPairAction 27 U) (Fin 27))
    (hsolvable : IsSolvable (P.complement ⟨0, by norm_num⟩)) :
    PreE7RankTailOwnerSourceData 27 U := by
  let x : Fin 27 := ⟨0, by norm_num⟩
  by_cases hnontrivial : Nontrivial (P.complement x)
  · letI : Nontrivial (P.complement x) := hnontrivial
    letI : IsSolvable (P.complement x) := hsolvable
    let D : SolubleDerivedLength (P.complement x) :=
      Classical.choice (SolubleDerivedLength.nonempty _ inferInstance)
    apply PrimitiveAffineSolubleOddOrderSource.toRankTailOwnerSource
      P (by norm_num) (by norm_num) hprimitive x D hgen
      (q := 78) (by norm_num)
        (primitiveAffineTwentySeven_soluble_card_le_without_catalogue P hprimitive x hsolvable)
    · norm_num [Nat.log]
    · exact window27
  · have hsub : Subsingleton (P.complement x) :=
      not_nontrivial_iff_subsingleton.mp hnontrivial
    letI : Subsingleton (P.complement x) := hsub
    let C : PrimitiveAffineDimensionOrderTailSource.CeilingData P := {
      m := 5
      width_lower := by norm_num
      order_le := by
        have hcomp : Nat.card (P.complement x) = 1 :=
          Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
        have hV : Nat.card P.V = 27 := by simpa using P.card_eq x
        rw [← (P.isComplement'_complement x).card_mul, hcomp, hV]
        norm_num
      slope_window := by
        norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree]
      menu_exponent := by norm_num }
    exact PrimitiveAffineDimensionOrderTailSource.toRankTailOwnerSource
      P C hprimitive x hgen

private noncomputable def solubleSource49
    (hgen : PermutationSubgroupGeneratorBound)
    (U : PreE7NonPairActionClass 49)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 49 U) (Fin 49))
    (P : PrimitiveAffineProfile (preE7NonPairAction 49 U) (Fin 49))
    (hsolvable : IsSolvable (P.complement ⟨0, by norm_num⟩)) :
    PreE7RankTailOwnerSourceData 49 U := by
  let x : Fin 49 := ⟨0, by norm_num⟩
  by_cases hnontrivial : Nontrivial (P.complement x)
  · letI : Nontrivial (P.complement x) := hnontrivial
    letI : IsSolvable (P.complement x) := hsolvable
    let D : SolubleDerivedLength (P.complement x) :=
      Classical.choice (SolubleDerivedLength.nonempty _ inferInstance)
    apply PrimitiveAffineSolubleOddOrderSource.toRankTailOwnerSource
      P (by norm_num) (by norm_num) hprimitive x D hgen
      (q := 49 ^ 2) (by norm_num)
        (P.complement_card_le_2401_degreeFortyNine hprimitive x)
    · norm_num [Nat.log]
    · exact window49
  · have hsub : Subsingleton (P.complement x) :=
      not_nontrivial_iff_subsingleton.mp hnontrivial
    letI : Subsingleton (P.complement x) := hsub
    let C : PrimitiveAffineDimensionOrderTailSource.CeilingData P := {
      m := 6
      width_lower := by norm_num
      order_le := by
        have hcomp : Nat.card (P.complement x) = 1 :=
          Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
        have hV : Nat.card P.V = 49 := by simpa using P.card_eq x
        rw [← (P.isComplement'_complement x).card_mul, hcomp, hV]
        norm_num
      slope_window := by
        norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree]
      menu_exponent := by norm_num }
    exact PrimitiveAffineDimensionOrderTailSource.toRankTailOwnerSource
      P C hprimitive x hgen

open PrimitiveAffineNonsolubleSmallNumerics
private theorem margin8
    (U : PreE7NonPairActionClass 8)
    (P : PrimitiveAffineProfile (preE7NonPairAction 8 U) (Fin 8))
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 8 U) (Fin 8))
    (x : Fin 8) (T : FixedTargetCompositionTrace (P.complement x))
    (hnonsolvable : ¬ IsSolvable (P.complement x)) :
    preE7CharacterRho * 8 ≤ ((evenWidth 8 : ℝ) - 2) / 8 -
      (fixedTargetCompositionGamma * T.envelope.abelianLength +
        P.bottomHalfSlope) := by
  apply P.nonsolubleEnvelope_exponent_margin_of_abelianLength
    (w := 8) (A := 0) T
  · rw [PrimitiveAffineDegreeEightActualConsumerFacts.nonsoluble_trace_abelianLength_eq_zero hprimitive P x (by simp) T hnonsolvable]
  · norm_num [preE7CharacterRho, evenWidth, halfDegree]

private theorem margin25
    (U : PreE7NonPairActionClass 25)
    (P : PrimitiveAffineProfile (preE7NonPairAction 25 U) (Fin 25))
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 25 U) (Fin 25))
    (x : Fin 25) (T : FixedTargetCompositionTrace (P.complement x))
    (hnonsolvable : ¬ IsSolvable (P.complement x)) :
    preE7CharacterRho * 25 ≤ ((evenWidth 25 : ℝ) - 2) / 8 -
      (fixedTargetCompositionGamma * T.envelope.abelianLength +
        P.bottomHalfSlope) := by
  apply P.nonsolubleEnvelope_exponent_margin_of_abelianLength
    (w := 25) (A := 3) T
    (degree25Data.nonsolubleComposition U P hprimitive x T hnonsolvable)
  norm_num [preE7CharacterRho, evenWidth, halfDegree]

private theorem margin27
    (U : PreE7NonPairActionClass 27)
    (P : PrimitiveAffineProfile (preE7NonPairAction 27 U) (Fin 27))
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 27 U) (Fin 27))
    (x : Fin 27) (T : FixedTargetCompositionTrace (P.complement x))
    (hnonsolvable : ¬ IsSolvable (P.complement x)) :
    preE7CharacterRho * 27 ≤ ((evenWidth 27 : ℝ) - 2) / 8 -
      (fixedTargetCompositionGamma * T.envelope.abelianLength +
        P.bottomHalfSlope) := by
  apply P.nonsolubleEnvelope_exponent_margin_of_abelianLength
    (w := 27) (A := 1) T
    (primitiveAffineTwentySeven_nonsoluble_abelianLength_le_one_without_catalogue P hprimitive x T hnonsolvable)
  norm_num [preE7CharacterRho, evenWidth, halfDegree]

private noncomputable def source8
    (U : PreE7NonPairActionClass 8)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 8 U) (Fin 8))
    (P : PrimitiveAffineProfile (preE7NonPairAction 8 U) (Fin 8))
    (hnonsolvable : ¬ IsSolvable
      (P.complement ⟨0, by norm_num⟩)) :
    PreE7RankTailOwnerSourceData 8 U := by
  let x : Fin 8 := ⟨0, by norm_num⟩
  let C := P.elementaryChart hprimitive
  let T := FixedTargetCompositionTrace.canonical (P.complement x)
  exact PrimitiveAffineNonsolubleSource.rankTailOwnerSourceDataOfMargin
    (by norm_num) (by norm_num) hprimitive P x C T hnonsolvable
    (margin8 U P hprimitive x T hnonsolvable)

private noncomputable def source8OfDegree
    {w : ℕ} (U : PreE7NonPairActionClass w)
    (hp : MulAction.IsPreprimitive (preE7NonPairAction w U) (Fin w))
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw : w = 8)
    (hn : ¬ IsSolvable (P.complement ⟨0, by omega⟩)) :
    PreE7RankTailOwnerSourceData w U := by
  subst w
  exact source8 U hp P hn

private noncomputable def source25
    (U : PreE7NonPairActionClass 25)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 25 U) (Fin 25))
    (P : PrimitiveAffineProfile (preE7NonPairAction 25 U) (Fin 25))
    (hnonsolvable : ¬ IsSolvable
      (P.complement ⟨0, by norm_num⟩)) :
    PreE7RankTailOwnerSourceData 25 U := by
  let x : Fin 25 := ⟨0, by norm_num⟩
  let C := P.elementaryChart hprimitive
  let T := FixedTargetCompositionTrace.canonical (P.complement x)
  exact PrimitiveAffineNonsolubleSource.rankTailOwnerSourceDataOfMargin
    (by norm_num) (by norm_num) hprimitive P x C T hnonsolvable
    (margin25 U P hprimitive x T hnonsolvable)

private noncomputable def source27
    (U : PreE7NonPairActionClass 27)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 27 U) (Fin 27))
    (P : PrimitiveAffineProfile (preE7NonPairAction 27 U) (Fin 27))
    (hnonsolvable : ¬ IsSolvable
      (P.complement ⟨0, by norm_num⟩)) :
    PreE7RankTailOwnerSourceData 27 U := by
  let x : Fin 27 := ⟨0, by norm_num⟩
  let C := P.elementaryChart hprimitive
  let T := FixedTargetCompositionTrace.canonical (P.complement x)
  exact PrimitiveAffineNonsolubleSource.rankTailOwnerSourceDataOfMargin
    (by norm_num) (by norm_num) hprimitive P x C T hnonsolvable
    (margin27 U P hprimitive x T hnonsolvable)

private noncomputable def degreeFiveSource
    (U : PreE7NonPairActionClass 5)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 5 U) (Fin 5))
    (P : PrimitiveAffineProfile (preE7NonPairAction 5 U) (Fin 5)) :
    PreE7RankTailOwnerSourceData 5 U :=
  match degreeFiveSource_of_publishedClassification DegreeFiveAffineClassification.classification U P hprimitive with
  | .inl S => .ordinary .saprim (.small S.numericalData)
  | .inr S => .f20 S.down

private noncomputable def source32OfDegree
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    {w : ℕ} (U : PreE7NonPairActionClass w)
    (hp : MulAction.IsPreprimitive (preE7NonPairAction w U) (Fin w))
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw : w = 32)
    (hn : ¬ IsSolvable (P.complement ⟨0, by omega⟩)) :
    PreE7RankTailOwnerSourceData w U := by
  subst w
  exact CFSGPrimitiveAffineBinaryFiveSource.source32 hindex U hp P hn

private noncomputable def source128OfDegree
    {w : ℕ} (U : PreE7NonPairActionClass w)
    (hp : MulAction.IsPreprimitive (preE7NonPairAction w U) (Fin w))
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw : w = 128)
    (hn : ¬ IsSolvable (P.complement ⟨0, by omega⟩)) :
    PreE7RankTailOwnerSourceData w U := by
  subst w
  exact CFSGPrimitiveAffineOrderTraceSources.source128 U hp P hn

private noncomputable def source256OfDegree
    {w : ℕ} (U : PreE7NonPairActionClass w)
    (hp : MulAction.IsPreprimitive (preE7NonPairAction w U) (Fin w))
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw : w = 256)
    (hn : ¬ IsSolvable (P.complement ⟨0, by omega⟩)) :
    PreE7RankTailOwnerSourceData w U := by
  subst w
  exact CFSGPrimitiveAffineOrderTraceSources.source256 U hp P hn

/-- Every primitive affine profile supplies an already integrated numerical
owner.  All infinite families are handled by proved generic estimates; the
finite structural input is used only in the explicitly displayed small
degrees. -/
noncomputable def primitiveOwnerAwaySixteenAndSixtyFour
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (hgen : PermutationSubgroupGeneratorBound)
    (hKP : KovacsPraegerAbelianizationBound)
    {w : ℕ} (U : PreE7NonPairActionClass w) (hw5 : 5 ≤ w)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hnot16 : w ≠ 16) (hnot64 : w ≠ 64) :
    PreE7RankTailOwnerSourceData w U := by
  by_cases hw1024 : 1024 ≤ w
  · exact primitiveAffineLarge_rankTailOwnerSourceData U hw1024 P
  have hw1024' : w < 1024 := by omega
  by_cases hw343 : 343 ≤ w
  · exact PrimitiveAffineOrderTailSource.toRankTailOwnerSource
      P hw343 hw1024' hprimitive ⟨0, by omega⟩ hgen
  have hw343' : w < 343 := by omega
  let x : Fin w := ⟨0, by omega⟩
  let d : ℕ := Classical.choose (P.degree_eq_prime_power x)
  have hdegree : w = P.p ^ d := Classical.choose_spec (P.degree_eq_prime_power x)
  have hclassification :=
    primePower_lt343_classification P.p_prime hdegree hw5 hw343'
  by_cases hweven : Even w
  · have hw6 : 6 ≤ w := by
      rcases hweven with ⟨k, hk⟩
      omega
    by_cases hsolvable : IsSolvable (P.complement x)
    · exact primitiveAffineEvenSoluble_rankTailOwnerSourceData
        U hw6 hw1024' hweven hprimitive P hsolvable
    · by_cases hw128 : 128 ≤ w
      · have hp2 : P.p = 2 := P.prime_eq_two_of_even_degree x hweven
        have htwo : w = 2 ^ d := by simpa [hp2] using hdegree
        have hdlo : 7 ≤ d := by
          by_contra h
          have hd : d ≤ 6 := by omega
          have he := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hd
          norm_num at he
          omega
        have hdhi : d ≤ 8 := by
          by_contra h
          have hd : 9 ≤ d := by omega
          have he := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hd
          norm_num at he
          omega
        have hcases : w = 128 ∨ w = 256 := by
          interval_cases d <;> norm_num at htwo ⊢ <;> omega
        by_cases h128 : w = 128
        · exact source128OfDegree U hprimitive P h128 (by simpa only [x] using hsolvable)
        · exact source256OfDegree U hprimitive P (hcases.resolve_left h128)
            (by simpa only [x] using hsolvable)
      · have hp2 : P.p = 2 := P.prime_eq_two_of_even_degree x hweven
        have htwo : w = 2 ^ d := by simpa [hp2] using hdegree
        have hsmall := twoPower_lt128_classification htwo hw5 (by omega)
        by_cases h8 : w = 8
        · exact source8OfDegree U hprimitive P h8 (by simpa only [x] using hsolvable)
        by_cases h16 : w = 16
        · exact False.elim (hnot16 h16)
        by_cases h32 : w = 32
        · exact source32OfDegree hindex U hprimitive P h32 (by simpa only [x] using hsolvable)
        · have h64 : w = 64 := by
            rcases hsmall with h | h | h | h
            · exact False.elim (h8 h)
            · exact False.elim (h16 h)
            · exact False.elim (h32 h)
            · exact h
          exact False.elim (hnot64 h64)
  by_cases hwprime : w.Prime
  · by_cases hw5eq : w = 5
    · subst w
      exact degreeFiveSource U hprimitive P
    · have hw6ne : w ≠ 6 := by
        intro h
        subst w
        norm_num at hwprime
      exact primitiveAffinePrimeDegree_rankTailOwnerSourceData
        U hwprime (by omega) hw1024' hprimitive P hKP
  by_cases h9 : w = 9
  · subst w
    exact primitiveAffineSolubleSmallCentral_rankTailOwnerSourceData
      solubleCentral hgen hKP
      U hprimitive P (Or.inl rfl)
      (P.complement_isSolvable_degreeNine hprimitive ⟨0, by norm_num⟩)
  by_cases h25 : w = 25
  · subst w
    by_cases hsolvable : IsSolvable (P.complement ⟨0, by norm_num⟩)
    · exact primitiveAffineSolubleSmallCentral_rankTailOwnerSourceData
        solubleCentral hgen hKP
        U hprimitive P (Or.inr rfl) hsolvable
    · exact source25 U hprimitive P hsolvable
  by_cases h27 : w = 27
  · subst w
    by_cases hsolvable : IsSolvable (P.complement ⟨0, by norm_num⟩)
    · exact solubleSource27 hgen U hprimitive P hsolvable
    · exact source27 U hprimitive P hsolvable
  by_cases h49 : w = 49
  · subst w
    by_cases hsolvable : IsSolvable (P.complement ⟨0, by norm_num⟩)
    · exact solubleSource49 hgen U hprimitive P hsolvable
    · exact CFSGPrimitiveAffineOrderTraceSources.source49 U hprimitive P hsolvable
  by_cases h81 : w = 81
  · subst w
    exact CFSGPrimitiveAffineEightyOneOrderSource.source U hprimitive P
  by_cases h121 : w = 121
  · exact PrimitiveAffineMediumOddSource.primitiveAffineMediumOdd_rankTailOwnerSourceData
      P hprimitive (Or.inl h121) hgen
  by_cases h125 : w = 125
  · exact PrimitiveAffineMediumOddSource.primitiveAffineMediumOdd_rankTailOwnerSourceData
      P hprimitive (Or.inr (Or.inl h125)) hgen
  by_cases h169 : w = 169
  · exact PrimitiveAffineMediumOddSource.primitiveAffineMediumOdd_rankTailOwnerSourceData
      P hprimitive (Or.inr (Or.inr (Or.inl h169))) hgen
  by_cases h243 : w = 243
  · exact PrimitiveAffineMediumOddSource.primitiveAffineMediumOdd_rankTailOwnerSourceData
      P hprimitive (Or.inr (Or.inr (Or.inr (Or.inl h243)))) hgen
  by_cases h289 : w = 289
  · exact PrimitiveAffineMediumOddSource.primitiveAffineMediumOdd_rankTailOwnerSourceData
      P hprimitive (Or.inr (Or.inr (Or.inr (Or.inr h289)))) hgen
  · exact False.elim (by
      rcases hclassification with h | h | h | h | h | h | h | h | h | h | h | h
      · exact hweven h
      · exact hwprime h
      · exact h9 h
      · exact h25 h
      · exact h27 h
      · exact h49 h
      · exact h81 h
      · exact h121 h
      · exact h125 h
      · exact h169 h
      · exact h243 h
      · exact h289 h)


end CFSGPrimitiveAffineOrderConsumer
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
