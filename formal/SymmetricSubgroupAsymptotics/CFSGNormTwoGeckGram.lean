import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRootGram

/-! The actual block Gram matrix for a norm-two Geck representation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckGram
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckHeightData CFSGNormTwoGeckStepMatrices CFSGNormTwoGeckRootGram
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

theorem cartan_symmetric (i j : b.support) : b.cartanMatrix i j=b.cartanMatrix j i := by
  apply (Int.cast_injective (α:=ℚ))
  change algebraMap ℤ ℚ (b.cartanMatrixIn ℤ i j)=algebraMap ℤ ℚ (b.cartanMatrixIn ℤ j i)
  rw [RootPairing.Base.algebraMap_cartanMatrixIn_apply,
    RootPairing.Base.algebraMap_cartanMatrixIn_apply]
  exact rational_symmetric A hs _ _

def gram : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ :=
  Matrix.fromBlocks (fun i j=>((|b.cartanMatrix i j|:ℤ):ℚ)) 0 0 (rootGram A hs hp)

theorem gram_symmetric : (gram A hs hp b).transpose=gram A hs hp b := by
  ext (i|i) (j|j)
  · simp [gram,cartan_symmetric A hs hp b]
  · rfl
  · rfl
  · exact congrFun (congrFun (rootGram_symmetric A hs hp) i) j

theorem step_skew (a : Roots A) (i : b.support) (ha : rootSign A a= -1)
    (hshift : ∀ j k,(rootPairing A hs hp).root k=
      (rootPairing A hs hp).root a+(rootPairing A hs hp).root j →
      rootSign A k= -rootSign A j) :
    (stepMatrix A hs hp b a i).transpose*gram A hs hp b+
      gram A hs hp b*stepMatrix A hs hp b a i=0 := by
  ext (j|j) (k|k)
  · simp [stepMatrix,gram,Matrix.mul_apply,Fintype.sum_sum_type]
  · by_cases hk : k=negativeIndex A hs hp a
    · subst k
      simp [stepMatrix,gram,rootGram,CFSGWeightedPermutationGram.gram,negativePerm,
        Matrix.mul_apply,Fintype.sum_sum_type,ite_mul,mul_ite,
        cartan_symmetric A hs hp b]
      rw [Finset.sum_eq_single a]
      · simp [ha]
      · intro x _ hxa
        simp [hxa]
      · simp
    · simp [stepMatrix,gram,rootGram,CFSGWeightedPermutationGram.gram,negativePerm,
        Matrix.mul_apply,Fintype.sum_sum_type,ite_mul,mul_ite,hk]
      rw [Finset.sum_eq_single a]
      · simp [hk]
      · intro x _ hxa
        simp [hxa]
      · simp
  · by_cases hj : j=negativeIndex A hs hp a
    · subst j
      have hsign : rootSign A (negativeIndex A hs hp a)= -1 :=
        (rootSign_negative A hs hp a).trans ha
      simp [stepMatrix,gram,rootGram,CFSGWeightedPermutationGram.gram,negativePerm,
        Matrix.mul_apply,Fintype.sum_sum_type,ite_mul,mul_ite,hsign,
        negativeIndex_involutive A hs hp a]
    · have hj' : a≠negativeIndex A hs hp j := by
        intro h
        apply hj
        simpa only [negativeIndex_involutive A hs hp j] using
          (congrArg (negativeIndex A hs hp) h).symm
      simp [stepMatrix,gram,rootGram,CFSGWeightedPermutationGram.gram,negativePerm,
        Matrix.mul_apply,Fintype.sum_sum_type,ite_mul,mul_ite,hj,hj']
  · have he := congrFun (congrFun (root_step_skew A hs hp a hshift) j) k
    simpa only [stepMatrix,gram,Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply,
      Fintype.sum_sum_type,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂,Pi.zero_apply,Matrix.zero_apply,zero_mul,mul_zero,Finset.sum_const_zero,
      zero_add,add_zero] using he

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckGram
