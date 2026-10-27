import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIntrinsicIntegralLattice
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDElementaryGroup

/-! Uniform parity preservation for the literal simple D roots. The chain
commutator has upper trace zero; the fork contributes twice a skew-block
entry. The second divided coefficient has zero upper trace. No rank table
or source-realization premise occurs. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIntrinsicRootOperatorParity
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIntrinsicIntegralLattice
open CFSGOrthogonalDCartanParityLattice
variable (r : ℕ) (hr : 4 ≤ r)

private theorem offdiagonal_blocks (X : Mat ℤ r)
    (hX : X∈skewAdjointMatricesLieSubalgebra (gram ℤ r)) (i j : Fin r) :
    X (.inl i) (.inr j)= -X (.inl j) (.inr i) ∧
      X (.inr i) (.inl j)= -X (.inr j) (.inl i) := by
  rw [mem_skewAdjointMatricesLieSubalgebra,mem_skewAdjointMatricesSubmodule] at hX
  change X.transpose*gram ℤ r=gram ℤ r*(-X) at hX
  have hB:=congrArg (fun M : Mat ℤ r=>M (.inr i) (.inr j)) hX
  have hC:=congrArg (fun M : Mat ℤ r=>M (.inl i) (.inl j)) hX
  simp [gram,Matrix.mul_apply,Fintype.sum_sum_type,Matrix.transpose_apply] at hB hC
  exact ⟨by linarith,by linarith⟩

include hr in
theorem root_commutator_trace (neg : Bool) (i : Fin r) (X : Mat ℤ r) :
    upperTrace r ⁅rootMatrix ℤ r neg i,X⁆=
      if hi : i.val+1 < r then 0 else
        if neg then X (.inl i) (.inr (previous r i))-
            X (.inl (previous r i)) (.inr i)
        else X (.inr i) (.inl (previous r i))-
            X (.inr (previous r i)) (.inl i) := by
  by_cases hi : i.val+1 < r
  · have hne : i≠(⟨i.val+1,hi⟩ : Fin r) := by
      intro h
      have hh:=congrArg Fin.val h
      change i.val=i.val+1 at hh
      omega
    cases neg <;>
      simp [upperTrace,CFSGOrthogonalDCartanIntrinsicCoordinates.total,diagonal,
        Ring.lie_def,rootMatrix,negative,positive,hi,Matrix.transpose_apply,
        Matrix.mul_apply,Fintype.sum_sum_type,Matrix.single_apply,Matrix.sub_apply,
        Finset.sum_sub_distrib,sub_mul,mul_sub,ite_mul,mul_ite,ite_and,hne,Ne.symm hne]
  · have hne : previous r i≠i := by
      intro h;have hh:=congrArg Fin.val h;have hil:=i.isLt
      dsimp [previous] at hh
      omega
    cases neg <;>
      simp [upperTrace,CFSGOrthogonalDCartanIntrinsicCoordinates.total,diagonal,
        Ring.lie_def,rootMatrix,negative,positive,hi,Matrix.transpose_apply,
        Matrix.mul_apply,Fintype.sum_sum_type,Matrix.single_apply,Matrix.sub_apply,
        Finset.sum_sub_distrib,sub_mul,mul_sub,ite_mul,mul_ite,ite_and,hne,Ne.symm hne]

include hr in
theorem root_sandwich_trace (neg : Bool) (i : Fin r) (X : Mat ℤ r) :
    upperTrace r (rootMatrix ℤ r neg i*X*rootMatrix ℤ r neg i)=0 := by
  by_cases hi : i.val+1 < r
  · have hne : i≠(⟨i.val+1,hi⟩ : Fin r) := by
      intro h
      have hh:=congrArg Fin.val h
      change i.val=i.val+1 at hh
      omega
    cases neg <;>
      simp [upperTrace,CFSGOrthogonalDCartanIntrinsicCoordinates.total,diagonal,
        rootMatrix,negative,positive,hi,Matrix.transpose_apply,Matrix.mul_apply,
        Fintype.sum_sum_type,Matrix.single_apply,Matrix.sub_apply,
        Finset.sum_sub_distrib,sub_mul,mul_sub,ite_mul,mul_ite,ite_and,hne,Ne.symm hne]
  · cases neg <;>
      simp [upperTrace,CFSGOrthogonalDCartanIntrinsicCoordinates.total,diagonal,
        rootMatrix,negative,positive,hi,Matrix.transpose_apply,Matrix.mul_apply,
        Fintype.sum_sum_type,Matrix.single_apply,Matrix.sub_apply,
        Finset.sum_sub_distrib,sub_mul,mul_sub,ite_mul,mul_ite,ite_and]

include hr in
theorem root_operator_mem (neg : Bool) (i : Fin r) (k : ℕ) (X : Mat ℤ r)
    (hX : X∈lattice r) : CFSGIntegralSquareZeroOperators.operator ℤ
      (rootMatrix ℤ r neg i) k X∈lattice r := by
  obtain ⟨horth,hpar⟩:=hX
  have hE : rootMatrix ℤ r neg i∈skewAdjointMatricesLieSubalgebra (gram ℤ r) := by
    cases neg
    · exact positive_mem_orthogonal ℤ r i
    · exact negative_mem_orthogonal ℤ r i
  refine ⟨operator_mem_orthogonal r _ _ hE horth k,?_⟩
  change diagonal r (CFSGIntegralSquareZeroOperators.operator ℤ (rootMatrix ℤ r neg i) k X)∈evenSum r
  by_cases hk : 3 ≤ k
  · rw [CFSGIntegralSquareZeroOperators.operator_large ℤ _ X k hk,map_zero]
    exact (evenSum r).zero_mem
  · have hlt : k < 3:=by omega
    interval_cases k
    · simpa only [CFSGIntegralSquareZeroOperators.operator_zero] using hpar
    · rw [mem_parity_iff,CFSGIntegralSquareZeroOperators.operator_one]
      change ∃ z : ℤ,upperTrace r ⁅rootMatrix ℤ r neg i,X⁆=2*z
      rw [root_commutator_trace r hr]
      by_cases hi : i.val+1 < r
      · rw [dif_pos hi]
        exact ⟨0,by ring⟩
      · rw [dif_neg hi]
        cases neg
        · have hs:=(offdiagonal_blocks r X horth i (previous r i)).2
          exact ⟨-X (.inr (previous r i)) (.inl i),by simp only [Bool.false_eq_true,if_false,if_true];rw [hs];ring⟩
        · have hs:=(offdiagonal_blocks r X horth i (previous r i)).1
          exact ⟨-X (.inl (previous r i)) (.inr i),by simp only [Bool.false_eq_true,if_false,if_true];rw [hs];ring⟩
    · rw [mem_parity_iff,CFSGIntegralSquareZeroOperators.operator_two,map_neg,
        root_sandwich_trace r hr]
      exact ⟨0,by ring⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIntrinsicRootOperatorParity
