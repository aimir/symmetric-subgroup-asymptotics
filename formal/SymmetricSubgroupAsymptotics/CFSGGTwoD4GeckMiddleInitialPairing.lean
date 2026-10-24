import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleCubicCurveWords
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleFixedPairing
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeLiePairing
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortOrbitCommutator

/-! The initial cubic coefficient pairs only with the final tensor
vertex. The actual primitive root commutator proves its nonzero scalar;
no table of all root-pair constants or guessed signs is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleInitialPairing

open CFSGTrialityD4NormTwo CFSGTrialityD4MiddleCube CFSGTrialityD4CubeComplement
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleFirstLayer
open CFSGTrialityGeckMiddleCubeCoordinates CFSGTrialityGeckMiddleSignedTensorBasis
open CFSGTrialityGeckMiddleOrderedTensor CFSGTrialityGeckMiddleTensorCovariance
open CFSGTrialityGeckMiddleCubeLiePairing CFSGTrialityGeckMiddleScalarPairing
open CFSGGTwoD4GeckMiddleCubicCurveWords CFSGGTwoD4GeckMiddleFixedCoordinates
open CFSGGTwoD4GeckMiddleFixedPairing CFSGFiniteFieldPolynomialCurveSpan
open CFSGTrialityGeckShortOrbitCommutator CFSGTrialityGeckFixedRootWords
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

private theorem final_vertex : cubeBits 7 = complement zeroCube := by
  funext j
  fin_cases j <;> rfl

def initialPairingCoefficient (K : Type) [Field K] : K :=
  highestFunctional K ⁅cubeCoefficient K zeroCube,actualTensor K 7⁆

theorem initial_pairing_row (K : Type) [Field K] (c : Fin 8 → K) :
    highestFunctional K ⁅cubeCoefficient K zeroCube,tensorCoordinates K c⁆ =
      c 7*initialPairingCoefficient K := by
  change highestFunctional K ⁅cubeCoefficient K zeroCube,∑ i : Fin 8,c i • actualTensor K i⁆ = _
  rw [lie_sum,map_sum]
  simp only [lie_smul,map_smul,smul_eq_mul]
  apply Finset.sum_eq_single 7
  · intro i _ hi
    have hne : cubeBits i ≠ complement zeroCube := by
      intro he
      exact hi (cubeBits_bijective.1 (he.trans final_vertex.symm))
    obtain ⟨e,_,he⟩ := tensorBasis_unit_sign (cubeBits i)
    have ht : actualTensor K i = (e : K) • cubeCoefficient K (cubeBits i) :=
      (tensorWord_eq K i).trans (he K)
    rw [ht,lie_smul,noncomplementary_coefficient_bracket K zeroCube (cubeBits i) hne,
      smul_zero,map_zero,mul_zero]
  · intro hnot
    exact (hnot (Finset.mem_univ 7)).elim

theorem initialPairingCoefficient_ne_zero (K : Type) [Field K] : initialPairingCoefficient K ≠ 0 := by
  obtain ⟨e,he,hvalue⟩ := tensorBasis_unit_sign (cubeBits 7)
  obtain ⟨d,hd,hbr⟩ := complementary_coefficient_bracket zeroCube
  have ht : actualTensor K 7 = (e : K) • cubeCoefficient K (complement zeroCube) := by
    exact (tensorWord_eq K 7).trans ((hvalue K).trans (congrArg (fun a => (e : K) • cubeCoefficient K a) final_vertex))
  have hc : initialPairingCoefficient K = (e : K)*(d : K) := by
    change highestFunctional K ⁅cubeCoefficient K zeroCube,actualTensor K 7⁆ = _
    rw [ht,lie_smul,hbr K,map_smul]
    let E : Mat K := CFSGNormTwoCoordinateRootBracketTransport.selectedFieldCoefficient
      (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K
      (CFSGTrialityD4PositiveRootOrbits.longRoot 2)
    have hval : highestFunctional K E = 1 := highestFunctional_highest K
    have hdval : highestFunctional K ((d : K) • E) = (d : K) :=
      ((highestFunctional K).map_smul (d : K) E).trans
        ((congrArg (fun a : K => (d : K)*a) hval).trans (mul_one _))
    simpa only [smul_eq_mul] using congrArg (fun a : K => (e : K) • a) hdval
  rw [hc]
  rcases he with rfl | rfl <;> rcases hd with rfl | rfl <;> norm_num

theorem initial_curve_pairing (K : Type) [Field K] (t : K) :
    pairing K (monomialCurve K 4 0) (monomialCurve K 4 t) = initialPairingCoefficient K*t^3 := by
  have hz : (fixedCubeEmbedding K (monomialCurve K 4 0)).val = cubeCoefficient K zeroCube := by
    rw [←normOrbit_one_coordinates]
    have hg : orderedOuterWord K 0 0 0 = 1 :=
      (ordered_equal_short K 0).trans (shortOrbit_zero K (RingEquiv.refl K) false)
    simp only [normOrbit,pow_one,one_pow]
    rw [hg,map_one]
    rfl
  change highestFunctional K ⁅(fixedCubeEmbedding K (monomialCurve K 4 0)).val,
    (fixedCubeEmbedding K (monomialCurve K 4 t)).val⁆ = _
  rw [hz]
  exact (initial_pairing_row K (orbitEmbedding K (monomialCurve K 4 t))).trans (mul_comm _ _)

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleInitialPairing
