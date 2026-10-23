import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionRootLabels
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylLatticeLinear
import Mathlib.Tactic.Ring

/-! The ACTUAL integral reflection word in the highest D4 root reverses
the original middle coordinate. Pure four-coordinate lattice steps are
identified with each actual simple reflection before calculating the
transport; no large Geck-index or inverse-word reduction is performed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityD4HighestMiddleReflection
open CFSGTrialityD4NormTwo CFSGTrialityGeckSectionRootLabels
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckLatticeDegree
open CFSGTrialityD4RelativeRootWords CFSGIntegerMatrixPairing
local notation "A" => CartanMatrix.D 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

def highestTransportLinear : (Fin 4 → ℤ) ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  wordLinear A hs hp Base Index (longWord 2)

def highestReflectionLinear : (Fin 4 → ℤ) ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  highestTransportLinear * (reflectionEquiv A (Index 1)).toIntLinearEquiv * highestTransportLinear⁻¹

private theorem wordLinear_apply_lattice (w : List (Fin 4)) (x : Fin 4 → ℤ) :
    wordLinear A hs hp Base Index w x = latticeWord w x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change latticeStep i (wordLinear A hs hp Base Index w x) = latticeStep i (latticeWord w x)
    rw [ih]

private theorem fin_two (h : 2 < 4) : (⟨2,h⟩ : Fin 4) = 2 := rfl
private theorem fin_three (h : 3 < 4) : (⟨3,h⟩ : Fin 4) = 3 := rfl
private theorem fin_succ_two : (2 : Fin 3).succ = (3 : Fin 4) := rfl

private theorem latticeStep_explicit (i : Fin 4) (x : Fin 4 → ℤ) :
    latticeStep i x =
      (![![-x 0+x 1,x 1,x 2,x 3], ![x 0,x 0-x 1+x 2+x 3,x 2,x 3],
        ![x 0,x 1,x 1-x 2,x 3], ![x 0,x 1,x 2,x 1-x 3]] : Fin 4 → Fin 4 → ℤ) i := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp only [latticeStep,integerPairing,Matrix.toBilin'_apply,Fin.sum_univ_succ,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply,
      CFSGTrialityD4PositiveRootOrbits.cartan_eq]
  all_goals norm_num [Fin.ext_iff,Fin.val_succ,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_succ,
    fin_two,fin_three,fin_succ_two] <;> first | rfl | ring

private theorem step_zero (x : Fin 4 → ℤ) :
    latticeStep 0 x = ![-x 0+x 1,x 1,x 2,x 3] := latticeStep_explicit 0 x
private theorem step_one (x : Fin 4 → ℤ) :
    latticeStep 1 x = ![x 0,x 0-x 1+x 2+x 3,x 2,x 3] := latticeStep_explicit 1 x
private theorem step_two (x : Fin 4 → ℤ) :
    latticeStep 2 x = ![x 0,x 1,x 1-x 2,x 3] := latticeStep_explicit 2 x
private theorem step_three (x : Fin 4 → ℤ) :
    latticeStep 3 x = ![x 0,x 1,x 2,x 1-x 3] := latticeStep_explicit 3 x

private theorem transport_middle (x : Fin 4 → ℤ) :
    (highestTransportLinear x) 1 = -x 0 + 2*x 1 - x 2 - x 3 := by
  rw [highestTransportLinear,wordLinear_apply_lattice]
  change latticeStep 1 (latticeStep 0 (latticeStep 2 (latticeStep 3 x))) 1 = _
  rw [step_three,step_two,step_zero,step_one]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,
    Matrix.cons_val_succ]
  ring

private theorem transport_reflection_middle (x : Fin 4 → ℤ) :
    (highestTransportLinear (reflectionEquiv A (Index 1) x)) 1 =
      -((highestTransportLinear x) 1) := by
  rw [transport_middle,transport_middle]
  change -(latticeStep 1 x 0) + 2*(latticeStep 1 x 1) -
    latticeStep 1 x 2 - latticeStep 1 x 3 = -(-x 0 + 2*x 1 - x 2 - x 3)
  rw [step_one]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,
    Matrix.cons_val_succ]
  ring

theorem highestReflection_middle (x : Fin 4 → ℤ) :
    (highestReflectionLinear x) 1 = -(x 1) := by
  change (highestTransportLinear
    (reflectionEquiv A (Index 1) (highestTransportLinear.symm x))) 1 = -(x 1)
  exact (transport_reflection_middle (highestTransportLinear.symm x)).trans
    (congrArg (fun y : Fin 4 → ℤ => -(y 1)) (highestTransportLinear.apply_symm_apply x))

end SymmetricSubgroupAsymptotics.CFSGTrialityD4HighestMiddleReflection
