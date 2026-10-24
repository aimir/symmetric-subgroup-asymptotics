import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleFixedRadicalCoordinates
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedLiftSpan
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldPolynomialCurveSpan
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeRootGenerated
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixBlockProjection

/-! Actual diagram-fixed middle words realizing every scalar multiple
of the cubic curve (1,t,t^2,t^3). Fixedness is proved from the actual
short-orbit and middle-root words, including characteristic three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleCubicCurveWords

open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleRadicalQuotient
open CFSGTrialityGeckMiddleFirstLayer CFSGTrialityGeckMiddleCubeCoordinates
open CFSGTrialityGeckMiddleCubeEdges CFSGTrialityGeckMiddleCubeLinearEdges
open CFSGTrialityGeckMiddleSignedTensorBasis CFSGTrialityGeckMiddleOrderedTensor
open CFSGTrialityGeckMiddleNormOrbitWords CFSGTrialityGeckMiddleFixedLiftSpan
open CFSGTrialityGeckShortComplement CFSGTrialityGeckMiddleRadicalCardinality
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckFixedRootWords
open CFSGTrialityGeckRootSubgroupTwist CFSGTrialityGeckMatrixTwist
open CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixSubgroups
open CFSGGradedMatrixBlockProjection
open CFSGGTwoD4GeckMiddleFixedCoordinates CFSGFiniteFieldPolynomialCurveSpan
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

def curveWord (K : Type) [Field K] (b t : K) : Raw K :=
  orderedOuterWord K t t t * cubeWord K zeroCube b * (orderedOuterWord K t t t)⁻¹

theorem ordered_equal_short (K : Type) [Field K] (t : K) :
    orderedOuterWord K t t t = shortOrbit K (RingEquiv.refl K) false t :=
  orderedOuterWord_eq_shortOrbit K (RingEquiv.refl K) t

theorem curveWord_mem_fixedMiddle (K : Type) [Field K] (b t : K) :
    curveWord K b t ∈ CFSGGTwoD4GeckMiddleFixedRadicalCoordinates.fixedMiddle K := by
  have hp : orderedOuterWord K t t t ∈ CFSGTrialityGeckPositiveTwist.Positive K := by
    rw [ordered_equal_short]
    exact shortOrbit_mem_rootGroup K (RingEquiv.refl K) false t
  have hn : orderedOuterWord K t t t ∈ Subgroup.normalizer (middleRadical K) := by
    rw [middleRadical_eq_shortComplement]
    exact positive_le_normalizer_shortComplement K hp
  have hmid : curveWord K b t ∈ middleRadical K :=
    (Subgroup.mem_normalizer_iff.mp hn _).mp (zeroCube_mem_middle K b)
  have hs : unitTwist K (RingEquiv.refl K) (orderedOuterWord K t t t) = orderedOuterWord K t t t := by
    rw [ordered_equal_short]
    exact shortOrbit_fixed K (RingEquiv.refl K) false t rfl
  have hz : unitTwist K (RingEquiv.refl K) (cubeWord K zeroCube b) = cubeWord K zeroCube b := by
    obtain ⟨e,_,he⟩ := zeroCube_word_sign
    rw [he,unitTwist_raw_root]
    rfl
  refine ⟨hmid,?_⟩
  change unitTwist K (RingEquiv.refl K) (curveWord K b t) = curveWord K b t
  simp only [curveWord,map_mul,map_inv,hs,hz]

theorem normOrbit_one_coordinates (K : Type) [Field K] (t : K) :
    normOrbit K 1 t = (fixedCubeEmbedding K (monomialCurve K 4 t)).val := by
  rw [normOrbit_coordinates]
  apply congrArg (CFSGTrialityGeckMiddleTensorCovariance.tensorCoordinates K)
  funext i
  fin_cases i <;> rfl

theorem curveWord_firstLayer (K : Type) [Field K] (b t : K) :
    firstLayer middleWeight (curveWord K b t) = b • (fixedCubeEmbedding K (monomialCurve K 4 t)).val := by
  have hg : orderedOuterWord K t t t ∈ preservingUnits middleWeight :=
    (preservingUnits middleWeight).mul_mem (outerWord_preserving K 2 t)
      ((preservingUnits middleWeight).mul_mem (outerWord_preserving K 1 t) (outerWord_preserving K 0 t))
  rw [curveWord,firstLayer_conjugate _ middleWeight _ _ hg
    ((preservingUnits middleWeight).inv_mem hg),cubeWord_firstLayer]
  change CFSGAlgebraConjugationAction.action K (Mat K) (orderedOuterWord K t t t)
    (b • cubeCoefficient K zeroCube) = _
  rw [map_smul]
  have he : CFSGAlgebraConjugationAction.action K (Mat K) (orderedOuterWord K t t t)
      (cubeCoefficient K zeroCube) = normOrbit K 1 t := by
    simp only [normOrbit,pow_one,one_pow]
  exact congrArg (fun M : Mat K => b • M) (he.trans (normOrbit_one_coordinates K t))

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleCubicCurveWords
