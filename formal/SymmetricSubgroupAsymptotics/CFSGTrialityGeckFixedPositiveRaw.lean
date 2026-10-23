import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortCentralizerCardinality
import SymmetricSubgroupAsymptotics.CFSGTrialityRelativeWordLanguage

/-! The actual fixed positive subgroup as a subgroup of raw Geck units,
with a typed membership criterion and relative-Weyl conjugation closure.
These are fixed-point statements, not a fixed-group recognition axiom. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveRaw
open CFSGTrialityGeckShortCentralizerCardinality CFSGTrialityGeckFixedPositiveGeneration
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckMatrixTwist CFSGTrialityRelativeWordLanguage
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord
open CFSGTrialityD4NormTwo CFSGSerreOrdinaryTwists
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

def fixedPositiveRaw (q : CFSG.PrimePower) :
    Subgroup ((Matrix GeckIndex GeckIndex (q.Extension 3))ˣ) :=
  (fixedPositiveInclusion (q.Extension 3) (definingFieldAutomorphism q 3)).range

theorem mem_fixedPositiveRaw_iff (q : CFSG.PrimePower)
    (x : (Matrix GeckIndex GeckIndex (q.Extension 3))ˣ) :
    x∈fixedPositiveRaw q ↔ x∈Positive (q.Extension 3) ∧
      unitTwist (q.Extension 3) (definingFieldAutomorphism q 3) x=x := by
  constructor
  · rintro ⟨u,rfl⟩
    refine ⟨u.val.property,?_⟩
    have hu := congrArg (fun v : Positive (q.Extension 3)=>v.val) u.property
    change (positiveTwist (q.Extension 3) (definingFieldAutomorphism q 3) u.val).val=
      u.val.val at hu
    rw [positiveTwist_val] at hu
    exact hu
  · rintro ⟨hpos,hfixed⟩
    let u : Positive (q.Extension 3) := ⟨x,hpos⟩
    have hu : positiveTwist (q.Extension 3) (definingFieldAutomorphism q 3) u=u := by
      apply Subtype.ext
      exact (positiveTwist_val (q.Extension 3) (definingFieldAutomorphism q 3) u).trans hfixed
    exact ⟨⟨u,hu⟩,rfl⟩

theorem relative_word_fixed (q : CFSG.PrimePower) (r : List Bool) :
    unitTwist (q.Extension 3) (definingFieldAutomorphism q 3)
      (wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite Base Index
        (q.Extension 3) (expandRelative r))=
    wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite Base Index
      (q.Extension 3) (expandRelative r) := by
  rw [word_eq_canonicalWord]
  exact CFSGTrialityRelativeWordLanguage.relative_word_fixed (q.Extension 3)
    (definingFieldAutomorphism q 3) r

theorem relative_conjugate_mem_of_positive (q : CFSG.PrimePower) (r : List Bool)
    (x : (Matrix GeckIndex GeckIndex (q.Extension 3))ˣ) (hx : x∈fixedPositiveRaw q)
    (hpos : (wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite Base Index
      (q.Extension 3) (expandRelative r))*x*
        (wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite Base Index
          (q.Extension 3) (expandRelative r))⁻¹∈Positive (q.Extension 3)) :
    (wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite Base Index
      (q.Extension 3) (expandRelative r))*x*
        (wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite Base Index
          (q.Extension 3) (expandRelative r))⁻¹∈fixedPositiveRaw q := by
  apply (mem_fixedPositiveRaw_iff q _).mpr
  refine ⟨hpos,?_⟩
  have hfixed := ((mem_fixedPositiveRaw_iff q x).mp hx).2
  rw [map_mul,map_mul,map_inv,relative_word_fixed,hfixed]

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveRaw
