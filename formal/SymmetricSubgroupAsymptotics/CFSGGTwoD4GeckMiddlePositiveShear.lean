import SymmetricSubgroupAsymptotics.CFSGCubicCurveTranslationLinear
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleCurveTranslation
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointProjection

/-! Actual positive short-root conjugation on the same fixed middle
radical. Its full four-coordinate action is obtained from the proved
cubic word translations and scalar spanning. The endpoint action in
characteristic three is a literal shear, without group recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddlePositiveShear

open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleRadicalQuotient
open CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckMiddleFirstLayer CFSGTrialityGeckMiddleCubeLinearEdges
open CFSGTrialityGeckMiddleCubeSpanActions CFSGTrialityGeckMiddleOrderedTensor
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckShortComplement CFSGTrialityGeckMiddleRadicalCardinality
open CFSGGradedMatrixSubgroups CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixBlockProjection
open CFSGGTwoD4GeckMiddleCubicCurveWords CFSGGTwoD4GeckMiddleCurveTranslation
open CFSGGTwoD4GeckMiddleFixedCoordinates CFSGGTwoD4GeckMiddleFixedRadicalCoordinates
open CFSGGTwoD4GeckMiddleEndpointProjection CFSGFiniteFieldPolynomialCurveSpan
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

private def matrixEmbedding (K : Type) [Field K] : (Fin 4 → K) →ₗ[K] Mat K :=
  (cubeSpan K).subtype.comp (fixedCubeEmbedding K)

theorem shortOrbit_preserving (K : Type) [Field K] (a : K) :
    shortOrbit K (RingEquiv.refl K) false a ∈ preservingUnits middleWeight := by
  have h : orderedOuterWord K a a a ∈ preservingUnits middleWeight :=
    (preservingUnits middleWeight).mul_mem (outerWord_preserving K 2 a)
      ((preservingUnits middleWeight).mul_mem (outerWord_preserving K 1 a)
        (outerWord_preserving K 0 a))
  rwa [ordered_equal_short] at h

theorem shortOrbit_conjugate_mem (K : Type) [Field K] (a : K) (u : fixedMiddle K) :
    shortOrbit K (RingEquiv.refl K) false a*u.val*
      (shortOrbit K (RingEquiv.refl K) false a)⁻¹ ∈ fixedMiddle K := by
  have hn : shortOrbit K (RingEquiv.refl K) false a ∈ Subgroup.normalizer (middleRadical K) := by
    rw [middleRadical_eq_shortComplement]
    exact positive_le_normalizer_shortComplement K (shortOrbit_mem_rootGroup K (RingEquiv.refl K) false a)
  refine ⟨(Subgroup.mem_normalizer_iff.mp hn u.val).mp u.property.1,?_⟩
  have hu : unitTwist K (RingEquiv.refl K) u.val = u.val := u.property.2
  change unitTwist K (RingEquiv.refl K) _ = _
  simp only [map_mul,map_inv,shortOrbit_fixed K (RingEquiv.refl K) false a rfl,hu]

def positiveConjugate (K : Type) [Field K] (a : K) : fixedMiddle K →* fixedMiddle K :=
  (((MulAut.conj (shortOrbit K (RingEquiv.refl K) false a)).toMonoidHom).comp
    (fixedMiddle K).subtype).codRestrict (fixedMiddle K) (shortOrbit_conjugate_mem K a)

theorem positiveConjugate_val (K : Type) [Field K] (a : K) (u : fixedMiddle K) :
    (positiveConjugate K a u).val = shortOrbit K (RingEquiv.refl K) false a*u.val*
      (shortOrbit K (RingEquiv.refl K) false a)⁻¹ := rfl

private theorem matrix_curve (K : Type) [Field K] (a t : K) :
    CFSGAlgebraConjugationAction.action K (Mat K) (shortOrbit K (RingEquiv.refl K) false a)
      (matrixEmbedding K (monomialCurve K 4 t)) = matrixEmbedding K (monomialCurve K 4 (a+t)) := by
  have hg := shortOrbit_preserving K a
  have h := congrArg (fun z : Raw K => firstLayer middleWeight z)
    (shortOrbit_conjugates_curve K a 1 t)
  dsimp only at h
  rw [firstLayer_conjugate K middleWeight _ _ hg ((preservingUnits middleWeight).inv_mem hg),
    curveWord_firstLayer,curveWord_firstLayer] at h
  simpa only [one_smul] using h

theorem shortOrbit_matrix_action (K : Type) [Field K] [Finite K]
    (hcard : 4 ≤ Nat.card K) (a : K) (c : Fin 4 → K) :
    CFSGAlgebraConjugationAction.action K (Mat K) (shortOrbit K (RingEquiv.refl K) false a)
      (fixedCubeEmbedding K c).val =
      (fixedCubeEmbedding K (CFSGCubicCurveTranslationLinear.translation a c)).val := by
  have h := CFSGCubicCurveTranslationLinear.map_eq_of_curve_translation hcard
    ((CFSGAlgebraConjugationAction.action K (Mat K)
      (shortOrbit K (RingEquiv.refl K) false a)).toLinearMap.comp (matrixEmbedding K))
    (matrixEmbedding K) a (matrix_curve K a)
  exact LinearMap.congr_fun h c

theorem coordinate_positiveConjugate (K : Type) [Field K] [Finite K]
    (hcard : 4 ≤ Nat.card K) (a : K) (u : fixedMiddle K) :
    coordinate K (positiveConjugate K a u) =
      CFSGCubicCurveTranslationLinear.translation a (coordinate K u) := by
  apply fixedCubeEmbedding_injective K
  apply Subtype.ext
  rw [coordinate_spec,positiveConjugate_val,
    firstLayer_conjugate K middleWeight _ _ (shortOrbit_preserving K a)
      ((preservingUnits middleWeight).inv_mem (shortOrbit_preserving K a)),
    ←coordinate_spec K u]
  exact shortOrbit_matrix_action K hcard a (coordinate K u)

theorem endpoint_positiveConjugate (K : Type) [Field K] [Finite K] [CharP K 3]
    (hcard : 4 ≤ Nat.card K) (a : K) (u : fixedMiddle K) :
    (endpointHom K (positiveConjugate K a u)).toAdd =
      ![(endpointHom K u).toAdd 0,
        a^3*(endpointHom K u).toAdd 0+(endpointHom K u).toAdd 1] := by
  change endpointLinear K (coordinate K (positiveConjugate K a u)) = _
  rw [coordinate_positiveConjugate K hcard]
  funext i
  fin_cases i
  · exact CFSGCubicCurveTranslationLinear.translation_first a (coordinate K u)
  · exact CFSGCubicCurveTranslationLinear.translation_last a (coordinate K u)

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddlePositiveShear
