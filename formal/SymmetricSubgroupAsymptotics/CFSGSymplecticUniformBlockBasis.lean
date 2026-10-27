import SymmetricSubgroupAsymptotics.CFSGSymplecticUniformBlockLie
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Uniform reconstruction of EVERY actual symplectic block matrix from
its primitive root/diagonal entries. This supplies complete natural
raising/lowering coefficient tables without a dimension theorem. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUniformBlockBasis
open CFSGSymplecticSerreMatrices CFSGSymplecticOriginalRootCandidates
open CFSGSymplecticUniformRootCoordinates CFSGSymplecticUniformBlockCoordinates
open CFSGSymplecticUniformBlockLie
variable (R : Type*) [CommRing R] (r : ℕ)

theorem matrix_mem (j : BasisIndex r) : Block R r (matrix R r j) := by
  rcases j with i | ⟨neg,j⟩
  · simp [Block,matrix,Matrix.single_apply,eq_comm,and_comm]
  · cases neg <;> rcases j with ij | (i | ij) <;>
      simp [Block,matrix,Matrix.single_apply,eq_comm,and_comm,add_comm]

theorem combination_coordinates (a : BasisIndex r→R) :
    coordinates R r (Fintype.linearCombination R (matrix R r) a)=a := by
  rw [Fintype.linearCombination_apply,map_sum]
  simp only [map_smul,coordinates_matrix]
  funext j
  simp [Finset.sum_apply,Pi.single_apply]

theorem combination_mem (a : BasisIndex r→R) :
    Block R r (Fintype.linearCombination R (matrix R r) a) := by
  apply (block_iff_mem_sp R r _).mpr
  rw [Fintype.linearCombination_apply]
  apply (LieAlgebra.Symplectic.sp (Fin r) R).sum_mem
  intro j hj
  exact (LieAlgebra.Symplectic.sp (Fin r) R).smul_mem (a j)
    ((block_iff_mem_sp R r _).mp (matrix_mem R r j))

theorem reconstruction (M : Mat R r) (hM : Block R r M) :
    Fintype.linearCombination R (matrix R r) (coordinates R r M)=M := by
  apply coordinates_injective R r _ M (combination_mem R r _) hM
  exact combination_coordinates R r _

/-- Genuine whole coefficient expansion for every pair of basis vectors. -/
theorem bracket_table (i j : BasisIndex r) :
    ⁅matrix R r i,matrix R r j⁆=
      Fintype.linearCombination R (matrix R r)
        (coordinates R r ⁅matrix R r i,matrix R r j⁆) :=
  (reconstruction R r _ (lie_mem R r _ _ (matrix_mem R r i) (matrix_mem R r j))).symm

end SymmetricSubgroupAsymptotics.CFSGSymplecticUniformBlockBasis
