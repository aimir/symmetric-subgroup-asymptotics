import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Literal three-coordinate determinant-one isometries fixing the
first singular vector are precisely one short-root family. No SO3/PSL2
identification or group-order formula is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGThreeDimensionalOrthogonalStabilizer
variable {K : Type*} [Field K]

def gram : Matrix (Fin 3) (Fin 3) K := !![0, 2, 0; 2, 0, 0; 0, 0, 1]

theorem first_column_stabilizer (h2 : (2 : K) ≠ 0) (A : Matrix (Fin 3) (Fin 3) K)
    (hf : A.transpose * gram * A = gram) (hd : A.det = 1)
    (h00 : A 0 0 = 1) (h10 : A 1 0 = 0) (h20 : A 2 0 = 0) :
    ∃ t : K, A = !![1, -(t ^ 2), t; 0, 1, 0; 0, -2 * t, 1] := by
  have hf01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 1) hf
  simp [gram, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, h00, h10, h20] at hf01
  have h11 : A 1 1 = 1 := by
    apply mul_left_cancel₀ h2
    linear_combination hf01
  have hf02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 2) hf
  simp [gram, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, h00, h10, h20] at hf02
  have h12 : A 1 2 = 0 := hf02.resolve_left h2
  have h22 : A 2 2 = 1 := by
    rw [Matrix.det_fin_three] at hd
    simpa only [h00, h10, h20, h11, h12, one_mul, mul_zero, zero_mul,
      sub_zero, zero_add, add_zero] using hd
  have hn := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 1 1) hf
  simp [gram, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, h11] at hn
  have hc := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 1 2) hf
  simp [gram, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, h11, h12, h22] at hc
  let t : K := -((2 : K)⁻¹ * A 2 1)
  have ht : (2 : K) * t = -(A 2 1) := by
    change 2 * (-(2⁻¹ * A 2 1)) = -(A 2 1)
    calc
      2 * (-(2⁻¹ * A 2 1)) = -(2 * 2⁻¹) * A 2 1 := by ring
      _ = -(A 2 1) := by rw [mul_inv_cancel₀ h2]; ring
  have h02 : A 0 2 = t := by
    apply mul_left_cancel₀ h2
    linear_combination hc - ht
  have h4 : (4 : K) ≠ 0 := by
    have he : (4 : K) = 2 * 2 := by ring
    rw [he]
    exact mul_ne_zero h2 h2
  have h01 : A 0 1 = -(t ^ 2) := by
    apply mul_left_cancel₀ h4
    have hs := congrArg (fun a : K => a ^ 2) ht
    linear_combination hn + hs
  have h21 : A 2 1 = -2 * t := by linear_combination ht
  refine ⟨t, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h10, h20, h11, h12, h22, h01, h02, h21]

end SymmetricSubgroupAsymptotics.CFSGThreeDimensionalOrthogonalStabilizer
