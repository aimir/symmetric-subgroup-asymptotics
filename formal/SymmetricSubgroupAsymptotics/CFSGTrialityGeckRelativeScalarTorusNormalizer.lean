import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeScalarTorus
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPairNormalizer
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckNormalizerEnvelopeTwist
import SymmetricSubgroupAsymptotics.CFSGFixedSubgroupConjugation

/-! The literal scalar-realizing words lie in the genuine fixed opposed
pair normalizer. Ambient torus containment and actual fixedness suffice;
no converse identification of that normalizer with a torus is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeScalarTorusNormalizer
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckRelativeScalarTorus CFSGTrialityGeckMixedTorusConjugation
open CFSGTrialityGeckShortTorusConjugation CFSGTrialityGeckShortParameterWeyl
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckFixedPairNormalizer
open CFSGTrialityGeckNormalizerEnvelopeTwist CFSGTrialityGeckNormalizerEnvelope
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckPositiveTwist
open CFSGTrialityNormTorusScalars CFSGTrialityFixedField CFSGSerreOrdinaryTwists
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckParameterizedTorus
open CFSGFixedSubgroupConjugation
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

 theorem shortTorusWord_mem_torus (K : Type) [Field K] (sigma : K≃+*K) (c : Kˣ) :
    shortTorusWord K sigma c∈torusGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K := by
  let T := torusGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K
  rw [shortTorusWord_eq_product]
  change parameterTorus (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K 0 c*
    parameterTorus (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K 2 (unitFieldMap K sigma c)*
    parameterTorus (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K 3 (unitFieldMap K sigma (unitFieldMap K sigma c))∈T
  exact T.mul_mem (T.mul_mem (Subgroup.subset_closure ⟨(0,c),rfl⟩)
    (Subgroup.subset_closure ⟨(2,unitFieldMap K sigma c),rfl⟩))
    (Subgroup.subset_closure ⟨(3,unitFieldMap K sigma (unitFieldMap K sigma c)),rfl⟩)

theorem relativeTorusWord_mem_pairNormalizer (q : CFSG.PrimePower)
    (c : (q.Extension 3)ˣ) (a : (fixedField q)ˣ) :
    relativeTorusWord q c a∈pairNormalizer (q.Extension 3) (definingFieldAutomorphism q 3) := by
  let d := relativeTorusWord q c a
  have hdJ := relativeTorusWord_mem_generated q c a
  have hdT : d∈torusGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index (q.Extension 3) :=
    (torusGroup _ _ _ _ _ _).mul_mem (shortTorusWord_mem_torus _ _ c)
      (Subgroup.subset_closure ⟨(1,embedUnits q a),rfl⟩)
  have hdD := torus_le_diagonalNormalizer (q.Extension 3) hdT
  have hdFix : unitTwist (q.Extension 3) (definingFieldAutomorphism q 3) d=d :=
    fixedRootGenerated_le_fixed _ _ hdJ
  have hp := normalizes_inf_fixed (unitTwist (q.Extension 3) (definingFieldAutomorphism q 3))
    (Positive (q.Extension 3)) d hdFix hdD.1.1
  have hn := normalizes_inf_fixed (unitTwist (q.Extension 3) (definingFieldAutomorphism q 3))
    (Negative (q.Extension 3)) d hdFix hdD.1.2
  exact ⟨⟨hp,hn⟩,hdJ⟩

theorem exists_scalar_word_in_pairNormalizer (q : CFSG.PrimePower)
    (x : (q.Extension 3)ˣ) (y : (fixedField q)ˣ) :
    ∃d∈pairNormalizer (q.Extension 3) (definingFieldAutomorphism q 3),
      (∀t,d*CFSGTrialityGeckFixedRootWords.shortOrbit (q.Extension 3)
          (definingFieldAutomorphism q 3) false t*d⁻¹=
        CFSGTrialityGeckFixedRootWords.shortOrbit (q.Extension 3)
          (definingFieldAutomorphism q 3) false ((x:q.Extension 3)*t))∧
      (∀t:fixedField q,d*CFSGSerreQuadraticMatrix.canonicalRoot rawData (q.Extension 3) false 1 t.val*d⁻¹=
        CFSGSerreQuadraticMatrix.canonicalRoot rawData (q.Extension 3) false 1 ((y:fixedField q)*t).val) := by
  obtain ⟨⟨c,a⟩,hca⟩ := scalarMap_surjective q (x,y)
  refine ⟨relativeTorusWord q c a,relativeTorusWord_mem_pairNormalizer q c a,?_,?_⟩
  · intro t
    simpa only [hca] using relativeTorusWord_short q c a t
  · intro t
    simpa only [hca] using relativeTorusWord_middle q c a t

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeScalarTorusNormalizer
