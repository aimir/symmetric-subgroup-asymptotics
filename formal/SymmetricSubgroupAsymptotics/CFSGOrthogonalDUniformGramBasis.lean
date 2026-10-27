import SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformGramCoordinates
import Mathlib.Tactic.Ring

/-! Whole rational orthogonal reconstruction from the literal D family.
Every bracket coefficient row is derived by reconstruction; no natural
or original source table oracle is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformGramBasis
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDOriginalRootCandidates
open CFSGOrthogonalDUniformRationalFamily CFSGOrthogonalDUniformGramCoordinates
variable (r : ℕ) (hr : 4 ≤ r)
local instance : DecidableEq (BasisIndex r) := Classical.decEq _

theorem matrix_mem (j : BasisIndex r) : Orthogonal r (matrix r j) := by
  rcases j with i | ⟨neg,ij | ij⟩
  · exact (skewAdjointMatricesLieSubalgebra (gram ℚ r)).lie_mem
      (positive_mem_orthogonal ℚ r i) (negative_mem_orthogonal ℚ r i)
  all_goals
    cases neg
    all_goals
      rw [Orthogonal,mem_skewAdjointMatricesLieSubalgebra,mem_skewAdjointMatricesSubmodule]
      change (matrix r _).transpose*gram ℚ r=gram ℚ r*(-matrix r _)
      simp only [matrix,CFSGOrthogonalDUniformRootCoordinates.matrix,
        CFSGOrthogonalDUniformRootMatrixArithmetic.difference,
        CFSGOrthogonalDUniformRootMatrixArithmetic.sumRoot,
        Matrix.transpose_sub,Matrix.transpose_single,Matrix.transpose_transpose,
        sub_mul,mul_sub,mul_neg]
      ext a b
      rcases a with a | a <;> rcases b with b | b <;>
        simp [gram,Matrix.mul_apply,Matrix.single,Fintype.sum_sum_type,ite_and,eq_comm] <;>
        (try split_ifs) <;> ring

theorem combination_coordinates (a : BasisIndex r→ℚ) :
    coordinates r hr (Fintype.linearCombination ℚ (matrix r) a)=a := by
  rw [Fintype.linearCombination_apply]
  simp only [map_sum,map_smul,CFSGOrthogonalDUniformRationalFamily.coordinates_matrix]
  funext j
  simp [Finset.sum_apply,Pi.single_apply]

theorem combination_mem (a : BasisIndex r→ℚ) :
    Orthogonal r (Fintype.linearCombination ℚ (matrix r) a) := by
  rw [Fintype.linearCombination_apply]
  apply (skewAdjointMatricesLieSubalgebra (gram ℚ r)).sum_mem
  intro j hj
  exact (skewAdjointMatricesLieSubalgebra (gram ℚ r)).smul_mem (a j) (matrix_mem r j)

theorem reconstruction (M : Mat ℚ r) (hM : Orthogonal r M) :
    Fintype.linearCombination ℚ (matrix r) (coordinates r hr M)=M := by
  apply CFSGOrthogonalDUniformGramCoordinates.coordinates_injective r hr _ M
    (combination_mem r _) hM
  exact combination_coordinates r hr _

theorem bracket_table (i j : BasisIndex r) :
    ⁅matrix r i,matrix r j⁆=
      Fintype.linearCombination ℚ (matrix r) (coordinates r hr ⁅matrix r i,matrix r j⁆) :=
  (reconstruction r hr _ ((skewAdjointMatricesLieSubalgebra (gram ℚ r)).lie_mem
    (matrix_mem r i) (matrix_mem r j))).symm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformGramBasis
