import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedLiftSpan
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortOrbitCommutator

/-! Actual short-root conjugation translates the literal cubic norm
curve. These are matrix equalities for the already constructed root
words, valid over every defining field; no abstract module recognition
or normalizer surjectivity is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckNormCurveTranslation
open CFSGTrialityMiddleFixedTensorSpan CFSGTrialityGeckMiddleNormOrbitWords
open CFSGTrialityGeckMiddleOrderedTensor CFSGTrialityGeckMiddleFixedLiftSpan
open CFSGTrialityGeckMiddleTensorCovariance CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckMiddleCubeCoordinates CFSGTrialityD4MiddleCube
open CFSGTrialityGeckMiddleFirstLayer CFSGTrialityGeckMiddleSignedTensorBasis
open CFSGCubicNormMonomialSeparation CFSGSerreOrdinaryTwists
open CFSGTrialityGeckFixedRootWords
local instance trialityCurveTranslateRootsDecidableEq :
    DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

private theorem linear_action_mul {F V G : Type*} [Field F] [AddCommGroup V]
    [Module F V] [Group G] (f : G →* (V ≃ₗ[F] V)) (g h : G) (v : V) :
    f g (f h v)=f (g*h) v := by
  rw [map_mul]
  rfl

private theorem normOrbit_as_action (q : CFSG.PrimePower) (t : K q) :
    normOrbit (K q) q.order t =
      CFSGAlgebraConjugationAction.action (K q) (Mat (K q)) (normWord q t)
        (cubeCoefficient (K q) zeroCube) := rfl

private theorem normWord_add (q : CFSG.PrimePower) (a t : K q) :
    normWord q (a+t)=normWord q a*normWord q t := by
  simp only [normWord_eq_shortOrbit,CFSGTrialityGeckShortOrbitCommutator.shortOrbit_add]

theorem normWord_normCurve (q : CFSG.PrimePower) (a t : K q) :
    CFSGAlgebraConjugationAction.action (K q) (Mat (K q)) (normWord q a)
      (tensorCoordinates (K q) (normCurve q.order t)) =
      tensorCoordinates (K q) (normCurve q.order (a+t)) := by
  rw [←normOrbit_coordinates,←normOrbit_coordinates]
  let f := CFSGAlgebraConjugationAction.action (K q) (Mat (K q))
  let v := cubeCoefficient (K q) zeroCube
  calc
    f (normWord q a) (normOrbit (K q) q.order t) =
        f (normWord q a) (f (normWord q t) v) :=
      congrArg (f (normWord q a)) (normOrbit_as_action q t)
    _ = f (normWord q a*normWord q t) v := linear_action_mul f _ _ v
    _ = f (normWord q (a+t)) v := congrArg (fun g => f g v) (normWord_add q a t).symm
    _ = normOrbit (K q) q.order (a+t) := (normOrbit_as_action q (a+t)).symm

theorem shortOrbit_normCurve (q : CFSG.PrimePower) (a t : K q) :
    CFSGAlgebraConjugationAction.action (K q) (Mat (K q))
      (shortOrbit (K q) (definingFieldAutomorphism q 3) false a)
      (tensorCoordinates (K q) (normCurve q.order t)) =
      tensorCoordinates (K q) (normCurve q.order (a+t)) := by
  rw [←normWord_eq_shortOrbit]
  exact normWord_normCurve q a t

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckNormCurveTranslation
