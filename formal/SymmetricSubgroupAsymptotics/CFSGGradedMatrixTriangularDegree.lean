import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSupport

/-! An invertible homogeneous matrix preserving a weak graded flag
cannot decrease the grading of a column. This uses literal degree support
and invertibility, without eigenvalues or one-dimensional weight spaces. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixTriangularDegree
open CFSGGradedMatrixSupport
variable {I V K : Type*} [Fintype I] [DecidableEq I] [Field K]

theorem degree_le_of_reverse_triangular (ell : I→V) (f : V→ℤ) (phi : V→V)
    (W : (Matrix I I K)ˣ) (hW : Supported ell phi (W : Matrix I I K))
    (htri : (W : Matrix I I K).BlockTriangular (fun i=> -f (ell i))) (j : I) :
    f (ell j)≤f (phi (ell j)) := by
  by_contra hn
  have hlt : f (phi (ell j))<f (ell j) := lt_of_not_ge hn
  have hz (i : I) : (W : Matrix I I K) i j=0 := by
    by_cases hi : ell i=phi (ell j)
    · apply htri
      change -f (ell j)< -f (ell i)
      rw [hi]
      omega
    · exact hW i j hi
  have hh := congrArg (fun M : Matrix I I K=>M j j) (Units.inv_mul W)
  dsimp only at hh
  simp only [Matrix.one_apply_eq] at hh
  change ((↑(W⁻¹) : Matrix I I K)*(W : Matrix I I K)) j j=1 at hh
  rw [Matrix.mul_apply] at hh
  simp only [hz,mul_zero,Finset.sum_const_zero] at hh
  exact zero_ne_one hh

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixTriangularDegree
