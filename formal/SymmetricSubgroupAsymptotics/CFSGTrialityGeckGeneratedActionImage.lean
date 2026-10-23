import SymmetricSubgroupAsymptotics.CFSGTrialityGeckDerivedRootGeneration
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeOpposition
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSourceRelativeWords

/-! The genuine fixed positive/negative generated action image equals
the SAME DERIVED ORIGINAL triality action range. Negative containment
uses an explicit ORIGINAL fixed opposition word and derived normality,
not an assumption that an arbitrary fixed matrix lifts to the source. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedActionImage
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckOriginalFixedSections
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckDerivedRootGeneration
open CFSGTrialityGeckRelativeOpposition CFSGTrialityGeckSourceRelativeWords
open CFSGTrialityGeckPositiveTwist CFSGTrialityGeckFixedPositiveDerivedImage
open CFSGTrialityGeckLongDerivedImage CFSGTrialityGeckMatrixTwist
open CFSGNormTwoGeckIntegralWord CFSGNormTwoGeckWeylWordDegree
open CFSGSerreOrdinaryTwists CFSGTrialityTripleFixedRoots

theorem matrixOpposition_val (K : Type) [Field K] :
    (matrixWord K oppositionWord).val = relativeOpposition K := by
  rw [matrixWord_val]
  change CFSGSerreQuadraticWeylWord.canonicalWord rawData K oppositionWord =
    wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite Base Index K oppositionWord
  rw [word_eq_canonicalWord]
  rfl

theorem positive_fixed_action_mem_derived (q : CFSG.PrimePower)
    (v : MatrixGroup (q.Extension 3))
    (hv : v.val ∈ signedFixed (q.Extension 3) (definingFieldAutomorphism q 3) false) :
    matrixAction (q.Extension 3) v ∈ (derivedImageAction q).range := by
  let u : Positive (q.Extension 3) := ⟨v.val,hv.1⟩
  have hfix : positiveTwist (q.Extension 3) (definingFieldAutomorphism q 3) u = u :=
    Subtype.ext hv.2
  exact fixed_positive_action_mem_derived_range q u hfix

theorem negative_fixed_action_mem_derived (q : CFSG.PrimePower)
    (v : MatrixGroup (q.Extension 3))
    (hv : v.val ∈ signedFixed (q.Extension 3) (definingFieldAutomorphism q 3) true) :
    matrixAction (q.Extension 3) v ∈ (derivedImageAction q).range := by
  rw [←fixed_positive_image_eq_fixed_negative (q.Extension 3) (definingFieldAutomorphism q 3)] at hv
  obtain ⟨u,hu,he⟩ := hv
  let up : Positive (q.Extension 3) := ⟨u,hu.1⟩
  have hfix : positiveTwist (q.Extension 3) (definingFieldAutomorphism q 3) up = up :=
    Subtype.ext hu.2
  obtain ⟨d,hd⟩ := exists_original_derived_action q up hfix
  let uH := positiveInclusion (q.Extension 3) up
  let O := matrixWord (q.Extension 3) oppositionWord
  let s := sourceRelativeWord q oppositionRelativeWord
  have hs : fixedImageAction q s = matrixAction (q.Extension 3) O :=
    sourceRelativeWord_action q oppositionRelativeWord
  have hd' : fixedImageAction q d.val = matrixAction (q.Extension 3) uH := hd
  have hmatrix : O*uH*O⁻¹ = v := by
    apply Subtype.ext
    change O.val*u*O.val⁻¹ = v.val
    dsimp only [O]
    rw [matrixOpposition_val]
    exact he
  have hm := conjugate_image_mem q s d.val (show fixedImageAction q d.val ∈
    (derivedImageAction q).range from ⟨d,rfl⟩)
  have ha : fixedImageAction q (s*d.val*s⁻¹) = matrixAction (q.Extension 3) v := by
    calc
      _ = matrixAction (q.Extension 3) (O*uH*O⁻¹) := by
        simp only [map_mul,map_inv,hs,hd']
      _ = _ := congrArg (matrixAction (q.Extension 3)) hmatrix
  exact ha ▸ hm

theorem signed_fixed_action_mem_derived (q : CFSG.PrimePower) (neg : Bool)
    (v : MatrixGroup (q.Extension 3))
    (hv : v.val ∈ signedFixed (q.Extension 3) (definingFieldAutomorphism q 3) neg) :
    matrixAction (q.Extension 3) v ∈ (derivedImageAction q).range := by
  cases neg
  · exact positive_fixed_action_mem_derived q v hv
  · exact negative_fixed_action_mem_derived q v hv

theorem generated_action_range_le_original_derived (q : CFSG.PrimePower) :
    (generatedAction (q.Extension 3) (definingFieldAutomorphism q 3)).range ≤
      (derivedImageAction q).range := by
  let R := (derivedImageAction q).range.comap (matrixAction (q.Extension 3))
  let RA := R.map (MatrixGroup (q.Extension 3)).subtype
  have hsign (neg : Bool) : signedFixed (q.Extension 3) (definingFieldAutomorphism q 3) neg ≤ RA := by
    intro u hu
    have hH := CFSGTrialityGeckFixedRangePreimage.signed_rootGroup_le_matrixGroup (q.Extension 3) neg hu.1
    exact ⟨⟨u,hH⟩,signed_fixed_action_mem_derived q neg ⟨u,hH⟩ hu,rfl⟩
  have hJ : fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3) ≤ RA :=
    sup_le (hsign false) (hsign true)
  rintro _ ⟨g,rfl⟩
  obtain ⟨v,hv,he⟩ := hJ g.property
  have he' : v = Subgroup.inclusion
      (CFSGTrialityGeckFixedRangePreimage.fixedRootGenerated_le_matrixGroup
        (q.Extension 3) (definingFieldAutomorphism q 3)) g := Subtype.ext he
  change matrixAction (q.Extension 3) _ ∈ (derivedImageAction q).range
  rw [←he']
  exact hv

theorem generated_action_range_eq_original_derived (q : CFSG.PrimePower) :
    (generatedAction (q.Extension 3) (definingFieldAutomorphism q 3)).range =
      (derivedImageAction q).range :=
  le_antisymm (generated_action_range_le_original_derived q) (original_derived_range_le_generated_action q)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedActionImage
