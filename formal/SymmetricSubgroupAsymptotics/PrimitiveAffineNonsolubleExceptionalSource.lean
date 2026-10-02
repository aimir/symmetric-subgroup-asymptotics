import SymmetricSubgroupAsymptotics.PrimitiveAffineNonsolubleSmallSource

/-!
# Exceptional nonsoluble primitive-affine degrees below 32

The published primitive-group tables give the composition factors of the
literal point stabilizer at degrees `8`, `16` and `27`.  At degree `25`, the
same statement follows from the standard identification
`PGL₂(5) ≅ S₅`.  We expose only those published composition-factor facts.
All fibre estimates, numerical margins and owner construction are proved in
Lean below.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open PrimitiveAffineNonsolubleSmallNumerics

/-- Published composition-factor information for the four exceptional
nonsoluble affine stabilizers.  `abelianLength` is independent of the chosen
composition series, so the statement applies to the canonical trace used by
the owner construction. -/
structure PublishedNonsolublePrimitiveAffineSmallCompositionInput where
  degreeEight : ∀ (U : PreE7NonPairActionClass 8)
    (P : PrimitiveAffineProfile (preE7NonPairAction 8 U) (Fin 8))
    (_hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 8 U) (Fin 8))
    (x : Fin 8) (T : FixedTargetCompositionTrace (P.complement x)),
    ¬ IsSolvable (P.complement x) → T.envelope.abelianLength = 0
  degreeSixteen : ∀ (U : PreE7NonPairActionClass 16)
    (P : PrimitiveAffineProfile (preE7NonPairAction 16 U) (Fin 16))
    (_hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 16 U) (Fin 16))
    (x : Fin 16) (T : FixedTargetCompositionTrace (P.complement x)),
    ¬ IsSolvable (P.complement x) → T.envelope.abelianLength ≤ 2
  degreeTwentyFive : ∀ (U : PreE7NonPairActionClass 25)
    (P : PrimitiveAffineProfile (preE7NonPairAction 25 U) (Fin 25))
    (_hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 25 U) (Fin 25))
    (x : Fin 25) (T : FixedTargetCompositionTrace (P.complement x)),
    ¬ IsSolvable (P.complement x) → T.envelope.abelianLength ≤ 3
  degreeTwentySeven : ∀ (U : PreE7NonPairActionClass 27)
    (P : PrimitiveAffineProfile (preE7NonPairAction 27 U) (Fin 27))
    (_hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 27 U) (Fin 27))
    (x : Fin 27) (T : FixedTargetCompositionTrace (P.complement x)),
    ¬ IsSolvable (P.complement x) → T.envelope.abelianLength ≤ 1

namespace PrimitiveAffineNonsolubleExceptionalSource

private theorem margin8
    (published : PublishedNonsolublePrimitiveAffineSmallCompositionInput)
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
  · rw [published.degreeEight U P hprimitive x T hnonsolvable]
  · norm_num [preE7CharacterRho, evenWidth, halfDegree]

private theorem margin16
    (published : PublishedNonsolublePrimitiveAffineSmallCompositionInput)
    (U : PreE7NonPairActionClass 16)
    (P : PrimitiveAffineProfile (preE7NonPairAction 16 U) (Fin 16))
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 16 U) (Fin 16))
    (x : Fin 16) (T : FixedTargetCompositionTrace (P.complement x))
    (hnonsolvable : ¬ IsSolvable (P.complement x)) :
    preE7CharacterRho * 16 ≤ ((evenWidth 16 : ℝ) - 2) / 8 -
      (fixedTargetCompositionGamma * T.envelope.abelianLength +
        P.bottomHalfSlope) := by
  apply P.nonsolubleEnvelope_exponent_margin_of_abelianLength
    (w := 16) (A := 2) T
    (published.degreeSixteen U P hprimitive x T hnonsolvable)
  norm_num [preE7CharacterRho, evenWidth, halfDegree]

private theorem margin25
    (published : PublishedNonsolublePrimitiveAffineSmallCompositionInput)
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
    (published.degreeTwentyFive U P hprimitive x T hnonsolvable)
  norm_num [preE7CharacterRho, evenWidth, halfDegree]

private theorem margin27
    (published : PublishedNonsolublePrimitiveAffineSmallCompositionInput)
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
    (published.degreeTwentySeven U P hprimitive x T hnonsolvable)
  norm_num [preE7CharacterRho, evenWidth, halfDegree]

private noncomputable def source8
    (published : PublishedNonsolublePrimitiveAffineSmallCompositionInput)
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
    (margin8 published U P hprimitive x T hnonsolvable)

private noncomputable def source16
    (published : PublishedNonsolublePrimitiveAffineSmallCompositionInput)
    (U : PreE7NonPairActionClass 16)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 16 U) (Fin 16))
    (P : PrimitiveAffineProfile (preE7NonPairAction 16 U) (Fin 16))
    (hnonsolvable : ¬ IsSolvable
      (P.complement ⟨0, by norm_num⟩)) :
    PreE7RankTailOwnerSourceData 16 U := by
  let x : Fin 16 := ⟨0, by norm_num⟩
  let C := P.elementaryChart hprimitive
  let T := FixedTargetCompositionTrace.canonical (P.complement x)
  exact PrimitiveAffineNonsolubleSource.rankTailOwnerSourceDataOfMargin
    (by norm_num) (by norm_num) hprimitive P x C T hnonsolvable
    (margin16 published U P hprimitive x T hnonsolvable)

private noncomputable def source25
    (published : PublishedNonsolublePrimitiveAffineSmallCompositionInput)
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
    (margin25 published U P hprimitive x T hnonsolvable)

private noncomputable def source27
    (published : PublishedNonsolublePrimitiveAffineSmallCompositionInput)
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
    (margin27 published U P hprimitive x T hnonsolvable)

/-- Every exceptional nonsoluble primitive affine profile supplies a
concrete NSAPRIM owner.  Only published stabilizer composition factors enter
as input. -/
noncomputable def rankTailOwnerSourceData
    {w : ℕ}
    (published : PublishedNonsolublePrimitiveAffineSmallCompositionInput)
    (U : PreE7NonPairActionClass w)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hdegree : w = 8 ∨ w = 16 ∨ w = 25 ∨ w = 27)
    (hnonsolvable : ¬ IsSolvable
      (P.complement ⟨0, by
        rcases hdegree with h | h | h | h <;> omega⟩)) :
    PreE7RankTailOwnerSourceData w U := by
  by_cases h8 : w = 8
  · subst w
    exact source8 published U hprimitive P hnonsolvable
  by_cases h16 : w = 16
  · subst w
    exact source16 published U hprimitive P hnonsolvable
  by_cases h25 : w = 25
  · subst w
    exact source25 published U hprimitive P hnonsolvable
  · have h27 : w = 27 := by
      rcases hdegree with h | h | h | h
      · exact False.elim (h8 h)
      · exact False.elim (h16 h)
      · exact False.elim (h25 h)
      · exact h
    subst w
    exact source27 published U hprimitive P hnonsolvable

end PrimitiveAffineNonsolubleExceptionalSource
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
