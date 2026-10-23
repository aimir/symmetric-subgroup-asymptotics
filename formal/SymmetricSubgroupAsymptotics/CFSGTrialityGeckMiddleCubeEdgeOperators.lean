import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeLinearEdges

/-! Integral signed cube edge operators extracted from the actual outer
conjugations. Every zero-bit edge has coefficient ±1 over the original
integers, so none disappears in characteristics two or three. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeEdgeOperators
open CFSGTrialityGeckDiagramCovariance CFSGTrialityD4MiddleCube
open CFSGTrialityGeckMiddleFirstLayer CFSGTrialityGeckMiddleCubeCoordinates
open CFSGTrialityGeckMiddleCubeLinearEdges
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

def edgeSign (a : Cube) (j : Fin 3) : ℤ :=
  if h : a j = 0 then Classical.choose (zero_bit_linear_sign a j h) else 0

theorem edgeSign_unit (a : Cube) (j : Fin 3) (hbit : a j = 0) :
    edgeSign a j = 1 ∨ edgeSign a j = -1 := by
  rw [edgeSign, dif_pos hbit]
  exact (Classical.choose_spec (zero_bit_linear_sign a j hbit)).1

theorem edgeSign_of_one (a : Cube) (j : Fin 3) (hbit : a j = 1) : edgeSign a j = 0 := by
  have hne : a j ≠ 0 := by
    intro h0
    have h := congrArg Fin.val (hbit.symm.trans h0)
    norm_num at h
  rw [edgeSign, dif_neg hne]

theorem outerLinear_cube (K : Type) [Field K] (a : Cube) (j : Fin 3) (t : K) :
    outerLinear K j t (cubeCoefficient K a) = cubeCoefficient K a +
      ((edgeSign a j : K)*t) • cubeCoefficient K (Function.update a j 1) := by
  by_cases h0 : a j = 0
  · have h := (Classical.choose_spec (zero_bit_linear_sign a j h0)).2 K t
    simpa only [edgeSign, dif_pos h0] using h
  · have hval : (a j).val ≠ 0 := fun h => h0 (Fin.ext h)
    have h1 : a j = 1 := by
      apply Fin.ext
      have hlt := (a j).isLt
      change (a j).val = 1
      omega
    rw [one_bit_linear_fixed K a j h1 t, edgeSign, dif_neg h0]
    simp only [Int.cast_zero, zero_mul, zero_smul, add_zero]

def edgeShift (K : Type) [Field K] (j : Fin 3) : Module.End K (Mat K) :=
  (outerLinear K j 1).toLinearMap - LinearMap.id

theorem edgeShift_cube (K : Type) [Field K] (a : Cube) (j : Fin 3) :
    edgeShift K j (cubeCoefficient K a) =
      (edgeSign a j : K) • cubeCoefficient K (Function.update a j 1) := by
  change outerLinear K j 1 (cubeCoefficient K a) - cubeCoefficient K a = _
  rw [outerLinear_cube, mul_one]
  abel

theorem outerLinear_cube_via_edgeShift (K : Type) [Field K] (a : Cube) (j : Fin 3) (t : K) :
    outerLinear K j t (cubeCoefficient K a) =
      cubeCoefficient K a + t • edgeShift K j (cubeCoefficient K a) := by
  rw [outerLinear_cube, edgeShift_cube, smul_smul, mul_comm t (edgeSign a j : K)]

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeEdgeOperators
