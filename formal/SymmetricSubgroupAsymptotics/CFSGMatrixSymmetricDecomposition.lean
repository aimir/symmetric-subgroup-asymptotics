import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Integral symmetric-matrix decomposition, without division by two. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGMatrixSymmetricDecomposition
variable {I : Type*} [Fintype I] [DecidableEq I] [LinearOrder I]
variable {R : Type*} [CommRing R]

def strictUpper (S : Matrix I I R) : Matrix I I R := fun i j => if i < j then S i j else 0

theorem symmetric_decomposition (S : Matrix I I R) (hS : S.IsSymm) :
    S = Matrix.diagonal (fun i => S i i) + strictUpper S + (strictUpper S).transpose := by
  ext i j
  by_cases he : i = j
  · subst j
    simp [strictUpper, Matrix.diagonal_apply]
  · rcases lt_or_gt_of_ne he with hlt | hgt
    · simp [strictUpper, Matrix.diagonal_apply_ne _ he, hlt, not_lt_of_gt hlt]
    · simp [strictUpper, Matrix.diagonal_apply_ne _ he, hgt, not_lt_of_gt hgt, hS.apply i j]

theorem diagonal_sum (S : Matrix I I R) :
    Matrix.diagonal (fun i => S i i) = ∑ i, Matrix.single i i (S i i) :=
  (Matrix.sum_single_eq_diagonal _).symm

theorem upper_transpose_sum (S : Matrix I I R) :
    strictUpper S + (strictUpper S).transpose =
      ∑ i, ∑ j, (Matrix.single i j (strictUpper S i j) +
        Matrix.single j i (strictUpper S i j)) := by
  simp only [Finset.sum_add_distrib]
  rw [Matrix.sum_sum_single]
  congr 1
  have h := congrArg Matrix.transpose (Matrix.sum_sum_single (strictUpper S))
  simpa only [Matrix.transpose_sum, Matrix.transpose_single] using h.symm

theorem mem_of_diagonal_and_pairs (P : AddSubgroup (Matrix I I R))
    (hdiag : ∀ i a, Matrix.single i i a ∈ P)
    (hpairs : ∀ i j, i ≠ j → ∀ a, Matrix.single i j a + Matrix.single j i a ∈ P)
    (S : Matrix I I R) (hS : S.IsSymm) : S ∈ P := by
  have hd : Matrix.diagonal (fun i => S i i) ∈ P := by
    rw [diagonal_sum]
    exact P.sum_mem (fun i _ => hdiag i (S i i))
  have hu : strictUpper S + (strictUpper S).transpose ∈ P := by
    rw [upper_transpose_sum]
    apply P.sum_mem
    intro i _
    apply P.sum_mem
    intro j _
    by_cases hij : i < j
    · exact hpairs i j (ne_of_lt hij) _
    · simp only [strictUpper, if_neg hij, Matrix.single_zero, add_zero]
      exact P.zero_mem
  rw [symmetric_decomposition S hS, add_assoc]
  exact P.add_mem hd hu

end SymmetricSubgroupAsymptotics.CFSGMatrixSymmetricDecomposition
