import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckDerivedRootGeneration
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeOpposition
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedPositiveDerivedImage
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSourceWordAction

/-! J has exactly the SAME Derived ORIGINAL pinned E6 action range.
The reverse containment uses whole fixed-U source coverage, an explicit
original fixed opposition word, and normality of the source commutator. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckGeneratedActionImage
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGTwistedE6GeckSourceAction
open CFSGTwistedE6GeckSourceWordAction CFSGTwistedE6FixedWeylWords
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckDerivedRootGeneration
open CFSGTwistedE6GeckRelativeOpposition CFSGTwistedE6RelativeOppositionLattice
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckFixedPositiveDerivedImage
open CFSGTwistedE6GeckPositiveActionInjective CFSGTwistedE6GeckMatrixTwist
open CFSGNormTwoGeckIntegralWord CFSGNormTwoGeckWeylWordDegree
open CFSGSerreOrdinaryTwists CFSGTwistedE6FixedA2

theorem matrixOpposition_val (K : Type) [Field K] :
    (matrixWord K oppositionWord).val = relativeOpposition K := by
  rw [matrixWord_val]
  change CFSGSerreQuadraticWeylWord.canonicalWord rawData K oppositionWord =
    wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K oppositionWord
  rw [word_eq_canonicalWord]

theorem positive_fixed_action_mem_derived (q : CFSG.PrimePower)
    (v : MatrixGroup (q.Extension 2))
    (hv : v.val ∈ signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) false) :
    matrixAction (q.Extension 2) v ∈ (derivedImageAction q).range := by
  let u : Positive (q.Extension 2) := ⟨v.val,hv.1⟩
  have hfix : positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2) u = u :=
    Subtype.ext hv.2
  obtain ⟨d,hd⟩ := exists_original_derived_positive_action q u hfix
  exact ⟨d,hd⟩

theorem negative_fixed_action_mem_derived (q : CFSG.PrimePower)
    (v : MatrixGroup (q.Extension 2))
    (hv : v.val ∈ signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) true) :
    matrixAction (q.Extension 2) v ∈ (derivedImageAction q).range := by
  rw [←fixed_positive_image_eq_fixed_negative (q.Extension 2) (definingFieldAutomorphism q 2)] at hv
  obtain ⟨u,hu,he⟩ := hv
  let up : Positive (q.Extension 2) := ⟨u,hu.1⟩
  have hfix : positiveTwist (q.Extension 2) (definingFieldAutomorphism q 2) up = up :=
    Subtype.ext hu.2
  obtain ⟨d,hd⟩ := exists_original_derived_positive_action q up hfix
  let uH := positiveInclusion (q.Extension 2) up
  let O := matrixWord (q.Extension 2) oppositionWord
  let s := sourceRelativeWord q oppositionRelativeWord
  have hs : imageAction q s = matrixAction (q.Extension 2) O :=
    sourceRelativeWord_action q oppositionRelativeWord
  have hd' : imageAction q d.val = matrixAction (q.Extension 2) uH := hd
  have hmatrix : O*uH*O⁻¹ = v := by
    apply Subtype.ext
    change O.val*u*O.val⁻¹ = v.val
    dsimp only [O]
    rw [matrixOpposition_val]
    exact he
  let ds : Derived q := ⟨s*d.val*s⁻¹,
    (inferInstance : (commutator (Fixed q)).Normal).conj_mem d.val d.property s⟩
  have hm : imageAction q (s*d.val*s⁻¹)∈(derivedImageAction q).range := ⟨ds,rfl⟩
  have ha : imageAction q (s*d.val*s⁻¹) = matrixAction (q.Extension 2) v := by
    calc
      _ = matrixAction (q.Extension 2) (O*uH*O⁻¹) := by
        simp only [map_mul,map_inv,hs,hd']
      _ = _ := congrArg (matrixAction (q.Extension 2)) hmatrix
  exact ha ▸ hm

theorem signed_fixed_action_mem_derived (q : CFSG.PrimePower) (neg : Bool)
    (v : MatrixGroup (q.Extension 2))
    (hv : v.val ∈ signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) neg) :
    matrixAction (q.Extension 2) v ∈ (derivedImageAction q).range := by
  cases neg
  · exact positive_fixed_action_mem_derived q v hv
  · exact negative_fixed_action_mem_derived q v hv

theorem generated_action_range_le_original_derived (q : CFSG.PrimePower) :
    (generatedAction (q.Extension 2) (definingFieldAutomorphism q 2)).range ≤
      (derivedImageAction q).range := by
  let R := (derivedImageAction q).range.comap (matrixAction (q.Extension 2))
  let RA := R.map (MatrixGroup (q.Extension 2)).subtype
  have hsign (neg : Bool) : signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) neg ≤ RA := by
    intro u hu
    have hH := CFSGTwistedE6GeckFixedRangePreimage.signed_rootGroup_le_matrixGroup (q.Extension 2) neg hu.1
    exact ⟨⟨u,hH⟩,signed_fixed_action_mem_derived q neg ⟨u,hH⟩ hu,rfl⟩
  have hJ : fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) ≤ RA :=
    sup_le (hsign false) (hsign true)
  rintro _ ⟨g,rfl⟩
  obtain ⟨v,hv,he⟩ := hJ g.property
  have he' : v = Subgroup.inclusion
      (CFSGTwistedE6GeckFixedRangePreimage.fixedRootGenerated_le_matrixGroup
        (q.Extension 2) (definingFieldAutomorphism q 2)) g := Subtype.ext he
  change matrixAction (q.Extension 2) _ ∈ (derivedImageAction q).range
  rw [←he']
  exact hv

theorem generated_action_range_eq_original_derived (q : CFSG.PrimePower) :
    (generatedAction (q.Extension 2) (definingFieldAutomorphism q 2)).range =
      (derivedImageAction q).range :=
  le_antisymm (generated_action_range_le_original_derived q) (original_derived_range_le_generated_action q)

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckGeneratedActionImage
