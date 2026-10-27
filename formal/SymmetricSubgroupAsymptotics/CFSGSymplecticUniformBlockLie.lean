import SymmetricSubgroupAsymptotics.CFSGSymplecticUniformBlockCoordinates
import Mathlib.Algebra.Lie.Classical

/-! The literal block predicate is exactly Mathlib's symplectic Lie
subalgebra. Thus every commutator remains in the same block space,
uniformly in rank and in characteristic. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUniformBlockLie
open CFSGSymplecticSerreMatrices CFSGSymplecticUniformBlockCoordinates
variable (R : Type*) [CommRing R] (r : ℕ)

private theorem fromBlocks_iff (A B C D : Matrix (Fin r) (Fin r) R) :
    Block R r (Matrix.fromBlocks A B C D) ↔
      (Matrix.J (Fin r) R).IsSkewAdjoint (Matrix.fromBlocks A B C D) := by
  change Block R r (Matrix.fromBlocks A B C D) ↔
    (Matrix.fromBlocks A B C D).transpose * Matrix.J (Fin r) R =
      Matrix.J (Fin r) R * (-Matrix.fromBlocks A B C D)
  simp only [Matrix.J,Matrix.fromBlocks_transpose,Matrix.fromBlocks_neg,
    Matrix.fromBlocks_multiply,mul_zero,zero_mul,zero_add,add_zero,mul_neg,neg_mul,
    Matrix.mul_one,Matrix.one_mul,neg_neg,neg_zero,Matrix.fromBlocks_inj]
  constructor
  · intro h
    refine ⟨?_,?_,?_,?_⟩
    · ext i j; exact (h.2.2 i j).symm
    · ext i j; exact (h.1 i j).symm
    · ext i j; exact h.1 j i
    · ext i j; exact congrArg Neg.neg (h.2.1 i j).symm
  · rintro ⟨hC,hD,hD',hB⟩
    refine ⟨?_,?_,?_⟩
    · intro i j; exact (congrFun (congrFun hD i) j).symm
    · intro i j
      have h:=congrFun (congrFun hB i) j
      exact (neg_injective h).symm
    · intro i j; exact (congrFun (congrFun hC i) j).symm

theorem block_iff_mem_sp (M : Mat R r) :
    Block R r M ↔ M∈LieAlgebra.Symplectic.sp (Fin r) R := by
  rw [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule]
  simpa only [Matrix.fromBlocks_toBlocks] using
    fromBlocks_iff R r M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂

theorem lie_mem (M N : Mat R r) (hM : Block R r M) (hN : Block R r N) :
    Block R r ⁅M,N⁆ := by
  apply (block_iff_mem_sp R r _).mpr
  exact (LieAlgebra.Symplectic.sp (Fin r) R).lie_mem
    ((block_iff_mem_sp R r M).mp hM) ((block_iff_mem_sp R r N).mp hN)

end SymmetricSubgroupAsymptotics.CFSGSymplecticUniformBlockLie
