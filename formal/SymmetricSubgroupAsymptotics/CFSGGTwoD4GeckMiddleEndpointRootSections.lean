import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointAxisCoefficients
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointNormalizerAction
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleWeylCubeSigns
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortOrbitCommutator

/-! Genuine first and last root-word sections of the endpoint axes. Their
coordinate signs are primitive integral units. Membership of the final
root line is obtained by the actual normalizing short Weyl word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointRootSections
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleFirstLayer
open CFSGTrialityGeckMiddleCubeEdges CFSGTrialityGeckMiddleCubeLinearEdges
open CFSGTrialityGeckMiddleSignedTensorBasis CFSGTrialityGeckMiddleOrderedTensor
open CFSGTrialityD4CubeComplement CFSGGTwoD4GeckMiddleWeylCubeSigns
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckShortOrbitCommutator
open CFSGGradedMatrixGroupFirstLayer CFSGGTwoD4GeckMiddleCubicCurveWords
open CFSGGTwoD4GeckMiddleCubicFixedLifts CFSGGTwoD4GeckMiddleFixedCoordinates
open CFSGGTwoD4GeckMiddleFixedRadicalCoordinates CFSGGTwoD4GeckMiddleEndpointAxisCoefficients
open CFSGGTwoD4GeckMiddleEndpointNormalizerAction
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

private theorem curve_zero (K : Type) [Field K] (b : K) :
    curveWord K b 0 = cubeWord K zeroCube b := by
  simp only [curveWord,ordered_equal_short,shortOrbit_zero,one_mul,inv_one,mul_one]

theorem first_root_coordinate (K : Type) [Field K] [Finite K]
    (u : fixedMiddle K) (b : K) (hu : u.val = cubeWord K zeroCube b) :
    coordinate K u = Pi.single 0 b := by
  apply fixedCubeEmbedding_injective K
  apply Subtype.ext
  have hf := congrArg (fun z : CFSGTrialityGeckMiddleRadicalQuotient.Raw K =>
    firstLayer middleWeight z) hu
  dsimp only at hf
  rw [cubeWord_firstLayer] at hf
  exact (coordinate_spec K u).trans (hf.trans (embedding_first_axis K b).symm)

theorem final_root_coordinates : ∃ d : ℤ, (d=1 ∨ d= -1) ∧
    ∀ (K : Type) [Field K] [Finite K] (u : fixedMiddle K) (b : K),
      u.val = cubeWord K (cubeBits 7) b → coordinate K u = Pi.single 3 ((d : K)*b) := by
  obtain ⟨d,hd,he⟩ := last_axis_unit_coefficient
  refine ⟨d,hd,?_⟩
  intro K _ _ u b hu
  have hd2 : (d : K)*((d : K)*b) = b := by
    rcases hd with rfl | rfl <;> simp
  have hb := (he K ((d : K)*b)).trans
    (congrArg (fun c : K => c • CFSGTrialityGeckMiddleCubeCoordinates.cubeCoefficient K (cubeBits 7)) hd2)
  apply fixedCubeEmbedding_injective K
  apply Subtype.ext
  have hf := congrArg (fun z : CFSGTrialityGeckMiddleRadicalQuotient.Raw K =>
    firstLayer middleWeight z) hu
  dsimp only at hf
  rw [cubeWord_firstLayer] at hf
  exact (coordinate_spec K u).trans (hf.trans hb.symm)

theorem final_root_mem (K : Type) [Field K] [Finite K] [CharP K 3] (b : K) :
    cubeWord K (cubeBits 7) b ∈ fixedMiddle K := by
  obtain ⟨e,he,hw⟩ := shortWeyl_cube_sign zeroCube
  have hlast : complement zeroCube = cubeBits 7 := by decide +kernel
  have he2 : (e : K)*((e : K)*b) = b := by
    rcases he with rfl | rfl <;> simp
  have h := ((fixedMiddle K).normalizerMonoidHom (shortWeylElement K)
    (curveElement K ((e : K)*b) 0)).property
  change shortWeyl K*curveWord K ((e : K)*b) 0*(shortWeyl K)⁻¹ ∈ fixedMiddle K at h
  rw [curve_zero,hw K ((e : K)*b),hlast,he2] at h
  exact h

def finalRootElement (K : Type) [Field K] [Finite K] [CharP K 3] (b : K) : fixedMiddle K :=
  ⟨cubeWord K (cubeBits 7) b,final_root_mem K b⟩

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointRootSections
