import SymmetricSubgroupAsymptotics.CFSGTrialityBinaryNormCurveBasis
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckNormCurveTranslation
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedTensorImage

/-! The regular translation action on the proved norm-curve basis is
exactly actual short-root conjugation under the faithful tensor embedding.
No named representation or full normalizer image is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityBinaryTensorTranslationAction
open Module CFSGTrialityMiddleFixedTensorSpan CFSGTrialityBinaryNormCurveBasis
open CFSGTrialityGeckMiddleFixedTensorImage CFSGTrialityGeckMiddleTensorCovariance
open CFSGTrialityGeckMiddleFirstLayer CFSGTrialityGeckFixedRootWords CFSGSerreOrdinaryTwists
local instance trialityBinaryTensorActionRootsDecidableEq :
    DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

def translationAction (q : CFSG.PrimePower) (hq : q.order=2) :
    Multiplicative (K q) →* (fullEnvelope q ≃ₗ[F q] fullEnvelope q) where
  toFun a := (curveBasis q hq).equiv (curveBasis q hq) (Equiv.addLeft a.toAdd)
  map_one' := by
    apply (curveBasis q hq).ext'
    intro t
    rw [Basis.equiv_apply]
    change curveBasis q hq (0+t)=curveBasis q hq t
    rw [zero_add]
  map_mul' a b := by
    apply (curveBasis q hq).ext'
    intro t
    change (curveBasis q hq).equiv (curveBasis q hq) (Equiv.addLeft (a.toAdd+b.toAdd))
      (curveBasis q hq t) =
      (curveBasis q hq).equiv (curveBasis q hq) (Equiv.addLeft a.toAdd)
        ((curveBasis q hq).equiv (curveBasis q hq) (Equiv.addLeft b.toAdd) (curveBasis q hq t))
    rw [Basis.equiv_apply,Basis.equiv_apply,Basis.equiv_apply]
    change curveBasis q hq ((a.toAdd+b.toAdd)+t)=curveBasis q hq (a.toAdd+(b.toAdd+t))
    rw [add_assoc]

theorem translationAction_curve (q : CFSG.PrimePower) (hq : q.order=2) (a t : K q) :
    translationAction q hq (Multiplicative.ofAdd a) (curve q t)=curve q (a+t) := by
  have h := (curveBasis q hq).equiv_apply t (curveBasis q hq) (Equiv.addLeft a)
  simpa only [curveBasis_apply] using h

theorem translationAction_matrix (q : CFSG.PrimePower) (hq : q.order=2)
    (a : K q) (c : fullEnvelope q) :
    fixedTensorEmbedding q (translationAction q hq (Multiplicative.ofAdd a) c) =
      CFSGAlgebraConjugationAction.action (K q) (Mat (K q))
        (shortOrbit (K q) (definingFieldAutomorphism q 3) false a) (fixedTensorEmbedding q c) := by
  let f := CFSGAlgebraConjugationAction.action (K q) (Mat (K q))
    (shortOrbit (K q) (definingFieldAutomorphism q 3) false a)
  have hmap : (fixedTensorEmbedding q).comp
      (translationAction q hq (Multiplicative.ofAdd a)).toLinearMap =
      (f.toLinearMap.restrictScalars (F q)).comp (fixedTensorEmbedding q) := by
    apply (curveBasis q hq).ext
    intro t
    change fixedTensorEmbedding q
      (translationAction q hq (Multiplicative.ofAdd a) (curveBasis q hq t)) =
      f (fixedTensorEmbedding q (curveBasis q hq t))
    rw [curveBasis_apply,translationAction_curve]
    change CFSGTrialityGeckMiddleTensorCovariance.tensorCoordinates (K q)
      (CFSGCubicNormMonomialSeparation.normCurve q.order (a+t)) =
      f (CFSGTrialityGeckMiddleTensorCovariance.tensorCoordinates (K q)
        (CFSGCubicNormMonomialSeparation.normCurve q.order t))
    exact (CFSGTrialityGeckNormCurveTranslation.shortOrbit_normCurve q a t).symm
  exact congrArg (fun L : fullEnvelope q →ₗ[F q] Mat (K q) => L c) hmap

end SymmetricSubgroupAsymptotics.CFSGTrialityBinaryTensorTranslationAction
