import SymmetricSubgroupAsymptotics.PrimitiveAffinePrimitiveConsumer
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightActualConsumerFacts
import SymmetricSubgroupAsymptotics.PrimitiveAffineTwentySevenNonsolubleConsumers
import SymmetricSubgroupAsymptotics.PrimitiveAffineTwentySevenSolubleConsumer
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenActualColdSource

/-! Actual primitive affine consumer with degree16 intercepted by its
original translation-kernel source. The finite data retain only the already
proved25/81/5 outputs; no degree16 composition statement is requested. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

structure ActualPrimitiveAffineFiniteData where
  degree25 : PublishedDegreeTwentyFiveLinearData
  degree81 : ∀ (U : PreE7NonPairActionClass 81)
    (P : PrimitiveAffineProfile (preE7NonPairAction 81 U) (Fin 81))
    (_hp : MulAction.IsPreprimitive (preE7NonPairAction 81 U) (Fin 81))
    (x : Fin 81),IsSolvable (P.complement x) → Nat.card (P.complement x) ≤ 81^3
  degreeFive : ∀ (U : PreE7NonPairActionClass 5)
    (_P : PrimitiveAffineProfile (preE7NonPairAction 5 U) (Fin 5))
    (_hp : MulAction.IsPreprimitive (preE7NonPairAction 5 U) (Fin 5)),
    PreE7SaprimDegreeFiveSource 5 U ⊕ PLift (PreE7F20Source 5 U)

namespace ActualPrimitiveAffineFiniteData

def solubleOdd (D : ActualPrimitiveAffineFiniteData) : PublishedSolublePrimitiveAffineExceptionalOrderInput where
  degreeTwentySeven := fun _ P hp x hs => primitiveAffineTwentySeven_soluble_card_le_without_catalogue P hp x hs
  degreeEightyOne := D.degree81

def solubleCentral (D : ActualPrimitiveAffineFiniteData) : PublishedSolublePrimitiveAffineSmallCentralInput where
  degreeTwentyFiveProjectiveDatum := D.degree25.solubleProjective

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
    (D : ActualPrimitiveAffineFiniteData)
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
    (D.degree25.nonsolubleComposition U P hprimitive x T hnonsolvable)
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
    (D : ActualPrimitiveAffineFiniteData)
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
    (margin25 D U P hprimitive x T hnonsolvable)

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
    (D : ActualPrimitiveAffineFiniteData)
    (U : PreE7NonPairActionClass 5)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 5 U) (Fin 5))
    (P : PrimitiveAffineProfile (preE7NonPairAction 5 U) (Fin 5)) :
    PreE7RankTailOwnerSourceData 5 U :=
  match D.degreeFive U P hprimitive with
  | .inl S => .ordinary .saprim (.small S.numericalData)
  | .inr S => .f20 S.down

/-- Every primitive affine profile supplies an already integrated numerical
owner.  All infinite families are handled by proved generic estimates; the
finite structural input is used only in the explicitly displayed small
degrees. -/
noncomputable def primitiveOwnerAwaySixteen
    (D : ActualPrimitiveAffineFiniteData)
    (hcomp : PrimitiveCompositionLengthInput)
    (hgen : PermutationSubgroupGeneratorBound)
    (hKP : KovacsPraegerAbelianizationBound)
    {w : ℕ} (U : PreE7NonPairActionClass w) (hw5 : 5 ≤ w)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hnot16 : w ≠ 16) :
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
      · exact PrimitiveAffineNonsolubleSource.canonicalRankTailOwnerSourceData
          hcomp hw128 (by omega) hprimitive P hsolvable
      · have hp2 : P.p = 2 := P.prime_eq_two_of_even_degree x hweven
        have htwo : w = 2 ^ d := by simpa [hp2] using hdegree
        have hsmall := twoPower_lt128_classification htwo hw5 (by omega)
        by_cases h8 : w = 8
        · exact source8OfDegree U hprimitive P h8 (by simpa only [x] using hsolvable)
        by_cases h16 : w = 16
        · exact False.elim (hnot16 h16)
        by_cases h32 : w = 32
        · exact PrimitiveAffineNonsolubleSmallSource.primitiveAffineNonsolubleSmall_rankTailOwnerSourceData
            hcomp U hprimitive P (Or.inl h32) hsolvable
        · have h64 : w = 64 := by
            rcases hsmall with h | h | h | h
            · exact False.elim (h8 h)
            · exact False.elim (h16 h)
            · exact False.elim (h32 h)
            · exact h
          exact PrimitiveAffineNonsolubleSmallSource.primitiveAffineNonsolubleSmall_rankTailOwnerSourceData
            hcomp U hprimitive P (Or.inr (Or.inr (Or.inl h64))) hsolvable
  by_cases hwprime : w.Prime
  · by_cases hw5eq : w = 5
    · subst w
      exact D.degreeFiveSource U hprimitive P
    · have hw6ne : w ≠ 6 := by
        intro h
        subst w
        norm_num at hwprime
      exact primitiveAffinePrimeDegree_rankTailOwnerSourceData
        U hwprime (by omega) hw1024' hprimitive P hKP
  by_cases h9 : w = 9
  · subst w
    exact primitiveAffineSolubleSmallCentral_rankTailOwnerSourceData
      D.solubleCentral hgen hKP
      U hprimitive P (Or.inl rfl)
      (P.complement_isSolvable_degreeNine hprimitive ⟨0, by norm_num⟩)
  by_cases h25 : w = 25
  · subst w
    by_cases hsolvable : IsSolvable (P.complement ⟨0, by norm_num⟩)
    · exact primitiveAffineSolubleSmallCentral_rankTailOwnerSourceData
        D.solubleCentral hgen hKP
        U hprimitive P (Or.inr rfl) hsolvable
    · exact source25 D U hprimitive P hsolvable
  by_cases h27 : w = 27
  · subst w
    by_cases hsolvable : IsSolvable (P.complement ⟨0, by norm_num⟩)
    · exact PrimitiveAffineSolubleOddExceptionalSource.rankTailOwnerSourceData
        D.solubleOdd hgen
        U hprimitive P (Or.inl rfl) hsolvable
    · exact source27 U hprimitive P hsolvable
  by_cases h49 : w = 49
  · subst w
    by_cases hsolvable : IsSolvable (P.complement ⟨0, by norm_num⟩)
    · exact PrimitiveAffineSolubleOddExceptionalSource.rankTailOwnerSourceData
        D.solubleOdd hgen
        U hprimitive P (Or.inr (Or.inl rfl)) hsolvable
    · exact PrimitiveAffineNonsolubleSmallSource.primitiveAffineNonsolubleSmall_rankTailOwnerSourceData
        hcomp U hprimitive P (Or.inr (Or.inl rfl)) hsolvable
  by_cases h81 : w = 81
  · subst w
    by_cases hsolvable : IsSolvable (P.complement ⟨0, by norm_num⟩)
    · exact PrimitiveAffineSolubleOddExceptionalSource.rankTailOwnerSourceData
        D.solubleOdd hgen
        U hprimitive P (Or.inr (Or.inr rfl)) hsolvable
    · exact PrimitiveAffineNonsolubleSmallSource.primitiveAffineNonsolubleSmall_rankTailOwnerSourceData
        hcomp U hprimitive P (Or.inr (Or.inr (Or.inr rfl))) hsolvable
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

/-- The original primitive16 action is intercepted before any unused
stronger stabilizer-composition package could be requested. -/
def primitiveSource
    (D : ActualPrimitiveAffineFiniteData)
    (hcomp : PrimitiveCompositionLengthInput) (hgen : PermutationSubgroupGeneratorBound)
    (hKP : KovacsPraegerAbelianizationBound)
    {w : ℕ} (U : PreE7NonPairActionClass w) (hw : 5 ≤ w)
    (hp : MulAction.IsPreprimitive (preE7NonPairAction w U) (Fin w))
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w)) :
    PreE7RankTailOwnerSourceData w U ⊕ PreE7RankTailSourceOrYonedaTopData w U := by
  by_cases h16 : w=16
  · subst w
    exact .inr (PrimitiveAffineSixteenActualColdSource.source P hp 0)
  · exact .inl (D.primitiveOwnerAwaySixteen hcomp hgen hKP U hw hp P h16)

end ActualPrimitiveAffineFiniteData
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
