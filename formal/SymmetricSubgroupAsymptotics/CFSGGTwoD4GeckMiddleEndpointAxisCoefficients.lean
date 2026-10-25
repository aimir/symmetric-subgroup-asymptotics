import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleFixedCoordinates

/-! Primitive coefficient coordinates for the two endpoint axes. The
last signed tensor vector is an integral unit times its actual original
root coefficient, uniformly over every field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointAxisCoefficients
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleFirstLayer
open CFSGTrialityGeckMiddleCubeCoordinates CFSGTrialityGeckMiddleSignedTensorBasis
open CFSGTrialityGeckMiddleOrderedTensor CFSGTrialityGeckMiddleTensorCovariance
open CFSGGTwoD4GeckMiddleFixedCoordinates
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

private theorem orbit_first_axis (K : Type) [Field K] (b : K) :
    orbitEmbedding K (Pi.single 0 b) = Pi.single 0 b := by
  funext i
  fin_cases i
  · change ((Pi.single (0 : Fin 4) b : Fin 4 → K) (0 : Fin 4)) =
      ((Pi.single (0 : Fin 8) b : Fin 8 → K) (0 : Fin 8))
    simp only [Pi.single_apply, Fin.reduceEq, if_true, if_false]
  · change ((Pi.single (0 : Fin 4) b : Fin 4 → K) (1 : Fin 4)) =
      ((Pi.single (0 : Fin 8) b : Fin 8 → K) (1 : Fin 8))
    simp only [Pi.single_apply, Fin.reduceEq, if_true, if_false]
  · change ((Pi.single (0 : Fin 4) b : Fin 4 → K) (1 : Fin 4)) =
      ((Pi.single (0 : Fin 8) b : Fin 8 → K) (2 : Fin 8))
    simp only [Pi.single_apply, Fin.reduceEq, if_true, if_false]
  · change ((Pi.single (0 : Fin 4) b : Fin 4 → K) (2 : Fin 4)) =
      ((Pi.single (0 : Fin 8) b : Fin 8 → K) (3 : Fin 8))
    simp only [Pi.single_apply, Fin.reduceEq, if_true, if_false]
  · change ((Pi.single (0 : Fin 4) b : Fin 4 → K) (1 : Fin 4)) =
      ((Pi.single (0 : Fin 8) b : Fin 8 → K) (4 : Fin 8))
    simp only [Pi.single_apply, Fin.reduceEq, if_true, if_false]
  · change ((Pi.single (0 : Fin 4) b : Fin 4 → K) (2 : Fin 4)) =
      ((Pi.single (0 : Fin 8) b : Fin 8 → K) (5 : Fin 8))
    simp only [Pi.single_apply, Fin.reduceEq, if_true, if_false]
  · change ((Pi.single (0 : Fin 4) b : Fin 4 → K) (2 : Fin 4)) =
      ((Pi.single (0 : Fin 8) b : Fin 8 → K) (6 : Fin 8))
    simp only [Pi.single_apply, Fin.reduceEq, if_true, if_false]
  · change ((Pi.single (0 : Fin 4) b : Fin 4 → K) (3 : Fin 4)) =
      ((Pi.single (0 : Fin 8) b : Fin 8 → K) (7 : Fin 8))
    simp only [Pi.single_apply, Fin.reduceEq, if_true, if_false]

private theorem orbit_last_axis (K : Type) [Field K] (b : K) :
    orbitEmbedding K (Pi.single 3 b) = Pi.single 7 b := by
  funext i
  fin_cases i
  · change ((Pi.single (3 : Fin 4) b : Fin 4 → K) (0 : Fin 4)) =
      ((Pi.single (7 : Fin 8) b : Fin 8 → K) (0 : Fin 8))
    simp only [Pi.single_apply, Fin.reduceEq, if_true, if_false]
  · change ((Pi.single (3 : Fin 4) b : Fin 4 → K) (1 : Fin 4)) =
      ((Pi.single (7 : Fin 8) b : Fin 8 → K) (1 : Fin 8))
    simp only [Pi.single_apply, Fin.reduceEq, if_true, if_false]
  · change ((Pi.single (3 : Fin 4) b : Fin 4 → K) (1 : Fin 4)) =
      ((Pi.single (7 : Fin 8) b : Fin 8 → K) (2 : Fin 8))
    simp only [Pi.single_apply, Fin.reduceEq, if_true, if_false]
  · change ((Pi.single (3 : Fin 4) b : Fin 4 → K) (2 : Fin 4)) =
      ((Pi.single (7 : Fin 8) b : Fin 8 → K) (3 : Fin 8))
    simp only [Pi.single_apply, Fin.reduceEq, if_true, if_false]
  · change ((Pi.single (3 : Fin 4) b : Fin 4 → K) (1 : Fin 4)) =
      ((Pi.single (7 : Fin 8) b : Fin 8 → K) (4 : Fin 8))
    simp only [Pi.single_apply, Fin.reduceEq, if_true, if_false]
  · change ((Pi.single (3 : Fin 4) b : Fin 4 → K) (2 : Fin 4)) =
      ((Pi.single (7 : Fin 8) b : Fin 8 → K) (5 : Fin 8))
    simp only [Pi.single_apply, Fin.reduceEq, if_true, if_false]
  · change ((Pi.single (3 : Fin 4) b : Fin 4 → K) (2 : Fin 4)) =
      ((Pi.single (7 : Fin 8) b : Fin 8 → K) (6 : Fin 8))
    simp only [Pi.single_apply, Fin.reduceEq, if_true, if_false]
  · change ((Pi.single (3 : Fin 4) b : Fin 4 → K) (3 : Fin 4)) =
      ((Pi.single (7 : Fin 8) b : Fin 8 → K) (7 : Fin 8))
    simp only [Pi.single_apply, Fin.reduceEq, if_true, if_false]

theorem embedding_first_axis (K : Type) [Field K] (b : K) :
    (fixedCubeEmbedding K (Pi.single 0 b)).val = b • cubeCoefficient K zeroCube := by
  change tensorCoordinates K (orbitEmbedding K (Pi.single 0 b)) = _
  rw [orbit_first_axis]
  exact Fintype.linearCombination_apply_single K (actualTensor K) 0 b

theorem embedding_last_axis (K : Type) [Field K] (b : K) :
    (fixedCubeEmbedding K (Pi.single 3 b)).val = b • actualTensor K 7 := by
  change tensorCoordinates K (orbitEmbedding K (Pi.single 3 b)) = _
  rw [orbit_last_axis]
  exact Fintype.linearCombination_apply_single K (actualTensor K) 7 b

theorem last_axis_unit_coefficient : ∃ d : ℤ, (d=1 ∨ d= -1) ∧
    ∀ (K : Type) [Field K] (b : K),
      (fixedCubeEmbedding K (Pi.single 3 b)).val =
        ((d : K)*b) • cubeCoefficient K (cubeBits 7) := by
  obtain ⟨d,hd,he⟩ := tensorBasis_unit_sign (cubeBits 7)
  refine ⟨d,hd,?_⟩
  intro K _ b
  have ht : actualTensor K 7 = (d : K) • cubeCoefficient K (cubeBits 7) :=
    (tensorWord_eq K 7).trans (he K)
  rw [embedding_last_axis,ht,smul_smul,mul_comm b (d : K)]

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointAxisCoefficients
