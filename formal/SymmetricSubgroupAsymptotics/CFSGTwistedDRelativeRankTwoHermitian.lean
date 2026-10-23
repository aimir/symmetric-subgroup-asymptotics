import SymmetricSubgroupAsymptotics.CFSGOrthogonalDForkPairAction
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! A coordinate pilot for the genuine rank-two natural base case.
The two commuting D2 root parameters act on the literal 2-by-2 matrix
by left and right elementary multiplication. Only this action formula
is asserted; no full fixed-isometry or SL2 identification is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeRankTwoHermitian
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGOrthogonalDForkPairAction
variable (K : Type) [Field K]

def matrixOfVector (v : Index 2 → K) : Matrix (Fin 2) (Fin 2) K :=
  !![v (Sum.inl 0), v (Sum.inl 1); v (Sum.inr 1), -v (Sum.inr 0)]

theorem matrixOfVector_injective : Function.Injective (matrixOfVector K) := by
  intro v w h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) h
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) h
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 1) h
  change v (Sum.inl 0) = w (Sum.inl 0) at h00
  change v (Sum.inl 1) = w (Sum.inl 1) at h01
  change v (Sum.inr 1) = w (Sum.inr 1) at h10
  change -v (Sum.inr 0) = -w (Sum.inr 0) at h11
  funext x
  cases x with
  | inl i => fin_cases i <;> assumption
  | inr i =>
    fin_cases i
    · exact neg_injective h11
    · exact h10

theorem determinant_matrixOfVector (v : Index 2 → K) :
    (matrixOfVector K v).det =
      -(v (Sum.inl 0) * v (Sum.inr 0) + v (Sum.inl 1) * v (Sum.inr 1)) := by
  rw [Matrix.det_fin_two]
  change v (Sum.inl 0) * -v (Sum.inr 0) - v (Sum.inl 1) * v (Sum.inr 1) = _
  ring

theorem paired_positive_action (a b : K) (v : Index 2 → K) :
    matrixOfVector K ((forkPair K 0 a b : Mat K 2) *ᵥ v) =
      Matrix.transvection (0 : Fin 2) 1 b * matrixOfVector K v *
        Matrix.transvection (1 : Fin 2) 0 a := by
  rw [forkPair_mulVec]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOfVector, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection,
      Matrix.single_apply, Matrix.one_apply, pen, last, Pi.single_apply] <;> ring

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeRankTwoHermitian
