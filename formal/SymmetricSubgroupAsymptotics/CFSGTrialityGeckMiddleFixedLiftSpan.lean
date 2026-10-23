import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedCommutators
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleTensorCovariance
import SymmetricSubgroupAsymptotics.CFSGTrialityMiddleFixedTensorSpan
import SymmetricSubgroupAsymptotics.CFSGAdditiveImageScalarSpan

/-! Constructive fixed-word lifts of all eight fixed tensor coordinates
and constructive derived-word lifts of all seven raised coordinates.
The scalar spans are mapped through actual first-layer homomorphisms;
fixed points are never presumed to lift through R -> R/Z. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedLiftSpan
open CFSGTrialityGeckDiagramCovariance CFSGTrialityD4MiddleCube
open CFSGTrialityGeckMiddleFirstLayer CFSGTrialityGeckMiddleCubeCoordinates
open CFSGTrialityGeckMiddleCubeSpanActions CFSGTrialityGeckMiddleSignedTensorBasis
open CFSGTrialityGeckMiddleCubeEdgeOperators CFSGTrialityGeckMiddleOrderedTensor
open CFSGTrialityGeckMiddleTensorCovariance CFSGTrialityGeckMiddleNormOrbitWords
open CFSGTrialityGeckMiddleFixedCommutators CFSGTrialityMiddleFixedTensorSpan
open CFSGGradedMatrixGroupFirstLayer CFSGCubicNormMonomialSeparation
open CFSGCubicNormCurveSpan CFSGOrderedCubeOperatorExpansion CFSGOrderedCubeNormOrbitSpan
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

theorem normOrbit_coordinates (K : Type) [Field K] (q : ℕ) (t : K) :
    normOrbit K q t = tensorCoordinates K (normCurve q t) := by
  rw [normOrbit_expansion]
  change (∑ i : Fin 8, normCurve q t i • tensorBasis K (cubeBits i)) =
    ∑ i : Fin 8, normCurve q t i • actualTensor K i
  simp only [actualTensor, tensorWord_eq]

def raisedTensorCoordinates (K : Type) [Field K] : (Fin 7 → K) →ₗ[K] Mat K :=
  Fintype.linearCombination K (fun i : Fin 7 => actualTensor K i.succ)

theorem normOrbit_difference_coordinates (K : Type) [Field K] (q : ℕ) (hq : 2 ≤ q) (t : K) :
    normOrbit K q t - cubeCoefficient K zeroCube =
      raisedTensorCoordinates K (augmentationCurve q t) := by
  rw [normOrbit, orderedOuterWord_action K _ _ _ _
    (Submodule.subset_span (Set.mem_range_self zeroCube))]
  exact orderedAction_sub_initial (edgeShift K 0) (edgeShift K 1) (edgeShift K 2)
    (cubeCoefficient K zeroCube) q hq t

theorem fixed_fullEnvelope_lifts (q : CFSG.PrimePower) (c : Fin 8 → q.Extension 3)
    (hc : c ∈ fullEnvelope q) :
    ∃ u : fixedMiddle q, firstLayer middleWeight u.val = tensorCoordinates (q.Extension 3) c := by
  let L := (tensorCoordinates (q.Extension 3)).restrictScalars (F q)
  have hfun : normOrbit (q.Extension 3) q.order = L ∘ normCurve q.order := by
    funext t
    exact normOrbit_coordinates _ _ t
  have hspan : Submodule.span (F q) (Set.range (normOrbit (q.Extension 3) q.order)) =
      (fullEnvelope q).map L := by
    rw [hfun, Set.range_comp, Submodule.span_image, normCurve_base_span]
  have hm : tensorCoordinates (q.Extension 3) c ∈
      Submodule.span (F q) (Set.range (normOrbit (q.Extension 3) q.order)) := by
    rw [hspan]
    exact ⟨c,hc,rfl⟩
  have hlift : ∀ (a : F q) (t : q.Extension 3), ∃ u : fixedMiddle q,
      fixedMiddleFirstLayerHom q u = Multiplicative.ofAdd
        (a • normOrbit (q.Extension 3) q.order t) := by
    intro a t
    refine ⟨⟨conjugateMiddleWord q a t,conjugateMiddleWord_mem_fixedMiddle q a t⟩,?_⟩
    apply congrArg Multiplicative.ofAdd
    change firstLayer middleWeight (conjugateMiddleWord q a t) =
      a.val • normOrbit (q.Extension 3) q.order t
    exact conjugateMiddleWord_firstLayer q a t
  obtain ⟨u,hu⟩ := CFSGAdditiveImageScalarSpan.span_lifts (fixedMiddleFirstLayerHom q)
    (normOrbit (q.Extension 3) q.order) hlift _ hm
  exact ⟨u,congrArg Multiplicative.toAdd hu⟩

theorem derived_raisedEnvelope_lifts (q : CFSG.PrimePower) (c : Fin 7 → q.Extension 3)
    (hc : c ∈ raisedEnvelope q) :
    ∃ u : derivedMiddle q, firstLayer middleWeight u.val = raisedTensorCoordinates (q.Extension 3) c := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  let L := (raisedTensorCoordinates (q.Extension 3)).restrictScalars (F q)
  let v := fun t : q.Extension 3 =>
    normOrbit (q.Extension 3) q.order t - cubeCoefficient (q.Extension 3) zeroCube
  have hfun : v = L ∘ augmentationCurve q.order := by
    funext t
    exact normOrbit_difference_coordinates _ _ hq t
  have hspan : Submodule.span (F q) (Set.range v) = (raisedEnvelope q).map L := by
    rw [hfun, Set.range_comp, Submodule.span_image, augmentationCurve_base_span]
  have hm : raisedTensorCoordinates (q.Extension 3) c ∈ Submodule.span (F q) (Set.range v) := by
    rw [hspan]
    exact ⟨c,hc,rfl⟩
  have hlift : ∀ (a : F q) (t : q.Extension 3), ∃ u : derivedMiddle q,
      derivedMiddleFirstLayerHom q u = Multiplicative.ofAdd (a • v t) := by
    intro a t
    refine ⟨⟨commutatorMiddleWord q a t,commutatorMiddleWord_mem_derivedMiddle q a t⟩,?_⟩
    apply congrArg Multiplicative.ofAdd
    change firstLayer middleWeight (commutatorMiddleWord q a t) =
      a.val • (normOrbit (q.Extension 3) q.order t - cubeCoefficient (q.Extension 3) zeroCube)
    exact commutatorMiddleWord_firstLayer q a t
  obtain ⟨u,hu⟩ := CFSGAdditiveImageScalarSpan.span_lifts (derivedMiddleFirstLayerHom q) v hlift _ hm
  exact ⟨u,congrArg Multiplicative.toAdd hu⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedLiftSpan
