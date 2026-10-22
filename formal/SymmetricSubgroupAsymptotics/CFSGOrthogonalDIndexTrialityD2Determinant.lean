import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexBundledQuadratic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! An exact original-coordinate realization of the residual D2
quadratic form as the determinant of a two-by-two matrix. This is a
linear coordinate equivalence, not a group-model identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticForm
variable (K : Type) [Field K]

def determinantCoordinates : (Index 2 → K) ≃ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun x := !![x (Sum.inl 0), x (Sum.inl 1); -x (Sum.inr 1), x (Sum.inr 0)]
  invFun A := Sum.elim ![A 0 0, A 0 1] ![A 1 1, -A 1 0]
  left_inv x := by
    funext i
    rcases i with i | i
    · fin_cases i <;> simp
    · fin_cases i <;> simp
  right_inv A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [add_comm]
  map_smul' a x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem determinantCoordinates_det (x : Index 2 → K) :
    Matrix.det (determinantCoordinates K x) = splitQuadraticForm K 2 x := by
  rw [splitQuadraticForm_apply]
  change Matrix.det !![x (Sum.inl 0), x (Sum.inl 1); -x (Sum.inr 1), x (Sum.inr 0)] =
    ∑ i : Fin 2, x (Sum.inl i) * x (Sum.inr i)
  rw [Matrix.det_fin_two_of, Fin.sum_univ_two]
  ring

theorem determinantCoordinates_singular_iff (x : Index 2 → K) :
    Matrix.det (determinantCoordinates K x) = 0 ↔ splitQuadraticForm K 2 x = 0 := by
  rw [determinantCoordinates_det]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
