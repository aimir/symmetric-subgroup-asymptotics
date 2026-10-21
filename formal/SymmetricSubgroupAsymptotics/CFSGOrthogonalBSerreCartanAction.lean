import SymmetricSubgroupAsymptotics.CFSGOrthogonalBCartanWeights
import SymmetricSubgroupAsymptotics.CFSGDiagonalMatrixLie

/-! The two Cartan-action relations for the actual B matrices. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices

theorem HE_integer (r : ℕ) (i j : Fin r) :
    ⁅cartan ℤ r i,positive ℤ r j⁆=CartanMatrix.C r i j • positive ℤ r j := by
  rw [cartan_eq_diagonal_weight]
  by_cases hj : j.val+1<r
  · simp only [positive,dif_pos hj,lie_sub]
    rw [CFSGDiagonalMatrixLie.diagonal_lie_single,CFSGDiagonalMatrixLie.diagonal_lie_single]
    simp only [mul_one,one_mul]
    rw [weight_chain r i j hj,weight_chain_mirror r i j hj]
    simp only [smul_sub,Matrix.smul_single,zsmul_eq_mul,mul_one,Int.cast_id]
  · simp only [positive,dif_neg hj,lie_sub]
    rw [CFSGDiagonalMatrixLie.diagonal_lie_single,CFSGDiagonalMatrixLie.diagonal_lie_single]
    simp only [weight_middle,weight_neg,weight_terminal r i j hj,sub_zero,zero_sub,
      neg_neg,mul_one,smul_sub,Matrix.smul_single,zsmul_eq_mul,Int.cast_id] <;>
      (ext a b <;> simp [Matrix.single] <;> split_ifs <;> ring)

theorem HF_integer (r : ℕ) (i j : Fin r) :
    ⁅cartan ℤ r i,negative ℤ r j⁆= -(CartanMatrix.C r i j • negative ℤ r j) := by
  rw [cartan_eq_diagonal_weight]
  by_cases hj : j.val+1<r
  · simp only [negative,dif_pos hj,lie_sub]
    rw [CFSGDiagonalMatrixLie.diagonal_lie_single,CFSGDiagonalMatrixLie.diagonal_lie_single]
    have hp := weight_chain r i j hj
    have hn := weight_chain_mirror r i j hj
    have hp' : weight r i (pos r (⟨j.val+1,hj⟩ : Fin r))-weight r i (pos r j)= -CartanMatrix.C r i j := by omega
    have hn' : weight r i (neg r j)-weight r i (neg r (⟨j.val+1,hj⟩ : Fin r))= -CartanMatrix.C r i j := by omega
    simp only [mul_one,one_mul]
    rw [hp',hn']
    simp only [mul_one,smul_sub,Matrix.smul_single,zsmul_eq_mul,Int.cast_id,
      neg_sub,neg_mul] <;>
      (ext a b <;> simp [Matrix.single] <;> split_ifs <;> ring)
  · simp only [negative,dif_neg hj,lie_sub]
    rw [CFSGDiagonalMatrixLie.diagonal_lie_single,CFSGDiagonalMatrixLie.diagonal_lie_single]
    simp only [weight_middle,weight_neg,weight_terminal r i j hj,sub_zero,zero_sub,
      mul_one,smul_sub,Matrix.smul_single,zsmul_eq_mul,Int.cast_id,
      neg_sub,neg_mul] <;>
      (ext a b <;> simp [Matrix.single] <;> split_ifs <;> ring)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
