import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! An invertible block-triangular matrix has a nonzero diagonal-block
part in each column. Blocks may have arbitrary size. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix
namespace SymmetricSubgroupAsymptotics.CFSGBlockTriangularColumn
variable {I L K : Type*} [Fintype I] [DecidableEq I] [LinearOrder L] [Field K]

theorem inverse_upper (weight : I → L) (A : (Matrix I I K)ˣ)
    (hA : (A : Matrix I I K).BlockTriangular weight) :
    (↑(A⁻¹) : Matrix I I K).BlockTriangular weight := by
  letI : Invertible (A : Matrix I I K) := A.invertible
  have hi : (A : Matrix I I K)⁻¹ = (↑(A⁻¹) : Matrix I I K) :=
    Matrix.inv_eq_left_inv (Units.inv_mul A)
  rw [← hi]
  exact Matrix.blockTriangular_inv_of_blockTriangular hA

def blockColumn (weight : I → L) (A : Matrix I I K) (j : I) : I → K :=
  fun i => if weight i = weight j then A i j else 0

theorem blockColumn_nonzero (weight : I → L) (A : (Matrix I I K)ˣ)
    (hA : (A : Matrix I I K).BlockTriangular weight) (j : I) :
    blockColumn weight (A : Matrix I I K) j ≠ 0 := by
  intro hz
  have hi := inverse_upper weight A hA
  have hc (i : I) (hij : weight i = weight j) : (A : Matrix I I K) i j = 0 := by
    have hh := congrFun hz i
    simpa only [blockColumn, if_pos hij, Pi.zero_apply] using hh
  have hp : ((↑(A⁻¹) : Matrix I I K) * (A : Matrix I I K)) j j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro i _
    rcases lt_trichotomy (weight i) (weight j) with h | h | h
    · rw [hi h, zero_mul]
    · rw [hc i h, mul_zero]
    · rw [hA h, mul_zero]
  have hone : ((↑(A⁻¹) : Matrix I I K) * (A : Matrix I I K)) j j = 1 := by
    have hh := congrArg (fun M : Matrix I I K => M j j) (Units.inv_mul A)
    simpa only [Matrix.one_apply_eq] using hh
  exact one_ne_zero (hone.symm.trans hp)

end SymmetricSubgroupAsymptotics.CFSGBlockTriangularColumn
