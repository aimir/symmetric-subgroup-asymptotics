import SymmetricSubgroupAsymptotics.CFSGOrthogonalDCartanWeights
import SymmetricSubgroupAsymptotics.CFSGDiagonalMatrixLie

/-! Both Cartan-action identities for the literal natural D matrices. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices

theorem cartan_eq_diagonal_weight (r : ℕ) (hr : 4≤r) (i : Fin r) :
    cartan ℤ r i=Matrix.diagonal (weight r i) := by
  obtain ⟨d,hd⟩ := cartan_isDiagonal ℤ r hr i
  have hw : weight r i=d := by
    funext x
    simp only [weight,hd,Matrix.diagonal_apply_eq]
  rw [hw]
  exact hd

theorem HE_integer (r : ℕ) (hr : 4≤r) (i j : Fin r) :
    ⁅cartan ℤ r i,positive ℤ r j⁆=CartanMatrix.D r i j • positive ℤ r j := by
  rw [cartan_eq_diagonal_weight r hr]
  by_cases hj : j.val+1<r
  · simp only [positive,dif_pos hj,lie_sub]
    rw [CFSGDiagonalMatrixLie.diagonal_lie_single,CFSGDiagonalMatrixLie.diagonal_lie_single]
    simp only [mul_one,one_mul]
    rw [weight_chain r hr i j hj]
    have hm : weight r i (Sum.inr (⟨j.val+1,hj⟩ : Fin r))-weight r i (Sum.inr j)=
        CartanMatrix.D r i j := by
      rw [weight_inr r hr,weight_inr r hr]
      have h := weight_chain r hr i j hj
      omega
    rw [hm]
    simp only [smul_sub,Matrix.smul_single,zsmul_eq_mul,mul_one,Int.cast_id]
  · simp only [positive,dif_neg hj,lie_sub]
    rw [CFSGDiagonalMatrixLie.diagonal_lie_single,CFSGDiagonalMatrixLie.diagonal_lie_single]
    simp only [mul_one,one_mul]
    have h1 : weight r i (Sum.inl (previous r j))-weight r i (Sum.inr j)=CartanMatrix.D r i j := by
      rw [weight_inr r hr,sub_neg_eq_add]
      exact weight_terminal r hr i j hj
    have h2 : weight r i (Sum.inl j)-weight r i (Sum.inr (previous r j))=CartanMatrix.D r i j := by
      rw [weight_inr r hr,sub_neg_eq_add,add_comm]
      exact weight_terminal r hr i j hj
    rw [h1,h2]
    simp only [smul_sub,Matrix.smul_single,zsmul_eq_mul,mul_one,Int.cast_id]

theorem HF_integer (r : ℕ) (hr : 4≤r) (i j : Fin r) :
    ⁅cartan ℤ r i,negative ℤ r j⁆=-(CartanMatrix.D r i j • negative ℤ r j) := by
  have ht := congrArg Matrix.transpose (HE_integer r hr i j)
  have hh : ⁅negative ℤ r j,cartan ℤ r i⁆=CartanMatrix.D r i j • negative ℤ r j := by
    simpa only [Ring.lie_def,Matrix.transpose_sub,Matrix.transpose_mul,
      cartan_transpose,Matrix.transpose_smul,negative] using ht
  exact (lie_skew (cartan ℤ r i) (negative ℤ r j)).symm.trans (congrArg Neg.neg hh)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
