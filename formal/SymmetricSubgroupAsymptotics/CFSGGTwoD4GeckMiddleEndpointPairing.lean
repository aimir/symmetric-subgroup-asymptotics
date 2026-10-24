import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleCurveTranslation
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleInitialPairing
import SymmetricSubgroupAsymptotics.CFSGCubicTranslationInvariantPairing
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCommutatorParameter

/-! The actual middle commutator form in characteristic three factors
through its two endpoint coordinates. Translation is proved from actual
source words and the injected highest-root parameter, then cubic spanning
extends the identity. The remaining central coordinates are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointPairing

open CFSGTrialityD4NormTwo CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleRadicalQuotient
open CFSGTrialityGeckMiddleFirstLayer CFSGGradedMatrixGroupFirstLayer
open CFSGTrialityGeckFixedRootWords CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoCoordinateAllRootParameters CFSGTrialityGeckMiddleCommutatorParameter
open CFSGGTwoD4GeckMiddleFixedCoordinates CFSGGTwoD4GeckMiddleFixedPairing
open CFSGGTwoD4GeckMiddleCubicCurveWords CFSGGTwoD4GeckMiddleCurveTranslation
open CFSGGTwoD4GeckMiddleInitialPairing CFSGFiniteFieldPolynomialCurveSpan
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance
open scoped commutatorElement

theorem curve_commutator (K : Type) [Field K] (s t : K) :
    selectedRootElement A hd hs hp ho K (longRoot 2)
      (pairing K (monomialCurve K 4 s) (monomialCurve K 4 t)) = ⁅curveWord K 1 s,curveWord K 1 t⁆ := by
  have hs' : firstLayer middleWeight (curveWord K 1 s) = (fixedCubeEmbedding K (monomialCurve K 4 s)).val := by
    simpa only [one_smul] using curveWord_firstLayer K 1 s
  have ht' : firstLayer middleWeight (curveWord K 1 t) = (fixedCubeEmbedding K (monomialCurve K 4 t)).val := by
    simpa only [one_smul] using curveWord_firstLayer K 1 t
  exact middle_pairing_commutator K
    ⟨curveWord K 1 s,(curveWord_mem_fixedMiddle K 1 s).1⟩
    ⟨curveWord K 1 t,(curveWord_mem_fixedMiddle K 1 t).1⟩
    (fixedCubeEmbedding K (monomialCurve K 4 s)) (fixedCubeEmbedding K (monomialCurve K 4 t)) hs' ht'

theorem curve_pairing_translation (K : Type) [Field K] (a s t : K) :
    pairing K (monomialCurve K 4 (a+s)) (monomialCurve K 4 (a+t)) =
      pairing K (monomialCurve K 4 s) (monomialCurve K 4 t) := by
  let g : Raw K := shortOrbit K (RingEquiv.refl K) false a
  let C : Raw K → Raw K := fun z => g*z*g⁻¹
  have hfix (b : K) : C (selectedRootElement A hd hs hp ho K (longRoot 2) b) =
      selectedRootElement A hd hs hp ho K (longRoot 2) b := by
    let z : Raw K := selectedRootElement A hd hs hp ho K (longRoot 2) b
    change g*z*g⁻¹ = z
    have hc : Commute g z := shortOrbit_highest_commute K a b
    rw [hc.eq]
    group
  have hconj : C ⁅curveWord K 1 s,curveWord K 1 t⁆ =
      ⁅curveWord K 1 (a+s),curveWord K 1 (a+t)⁆ := by
    calc
      _ = ⁅g*curveWord K 1 s*g⁻¹,g*curveWord K 1 t*g⁻¹⁆ := by
        dsimp only [C]
        simp only [commutatorElement_def]
        group
      _ = _ := congrArg₂ (fun u v : Raw K => ⁅u,v⁆)
        (shortOrbit_conjugates_curve K a 1 s) (shortOrbit_conjugates_curve K a 1 t)
  have hroot := (curve_commutator K (a+s) (a+t)).trans
    (hconj.symm.trans ((congrArg C (curve_commutator K s t).symm).trans (hfix _)))
  exact congrArg Multiplicative.toAdd
    (selected_rootHom_injective A hd hs hp ho K (longRoot 2) hroot)

theorem pairing_eq_endpoint_char_three (K : Type) [Field K] [Finite K] [CharP K 3]
    (hcard : 4 ≤ Nat.card K) :
    pairing K = CFSGCubicTranslationInvariantPairing.endpointPairing (initialPairingCoefficient K) :=
  CFSGCubicTranslationInvariantPairing.pairing_eq_endpoint hcard (pairing K) (initialPairingCoefficient K)
    (initial_curve_pairing K) (curve_pairing_translation K)

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointPairing
