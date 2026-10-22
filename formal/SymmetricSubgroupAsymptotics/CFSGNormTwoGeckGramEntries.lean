import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckGram
import Mathlib.Algebra.Lie.SkewAdjoint
import Mathlib.Tactic.Linarith

/-! Sparse entries of the actual height form. Its skew condition kills the
opposite-root entry needed by the fourth conjugation coefficient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckGramEntries
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckHeightData CFSGNormTwoGeckStepMatrices CFSGNormTwoGeckGram
open CFSGNormTwoGeckRootGram
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

theorem gram_mul_root (X : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)
    (i : Roots A) (j : b.support⊕Roots A) :
    (gram A hs hp b*X) (.inr i) j=rootSign A i*X (.inr (negativeIndex A hs hp i)) j := by
  simp [gram,rootGram,CFSGWeightedPermutationGram.gram,negativePerm,
    Matrix.mul_apply,Fintype.sum_sum_type,ite_mul]

theorem transpose_mul_gram_root (X : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)
    (i : Roots A) (j : b.support⊕Roots A) :
    (X.transpose*gram A hs hp b) j (.inr i)=
      X (.inr (negativeIndex A hs hp i)) j*rootSign A i := by
  calc
    _=((X.transpose*gram A hs hp b).transpose) (.inr i) j := rfl
    _=((gram A hs hp b).transpose*X) (.inr i) j := by
      rw [Matrix.transpose_mul,Matrix.transpose_transpose]
    _=(gram A hs hp b*X) (.inr i) j := by rw [gram_symmetric A hs hp b]
    _=_ := by rw [gram_mul_root A hs hp b,mul_comm]

theorem opposite_entry_zero (X : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)
    (hX : X∈skewAdjointMatricesLieSubalgebra (gram A hs hp b)) (i : Roots A) :
    X (.inr (negativeIndex A hs hp i)) (.inr i)=0 := by
  rw [mem_skewAdjointMatricesLieSubalgebra,mem_skewAdjointMatricesSubmodule] at hX
  change X.transpose*gram A hs hp b=gram A hs hp b*(-X) at hX
  have hh := congrArg (fun M : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ=>
    M (.inr i) (.inr i)) hX
  dsimp only at hh
  rw [transpose_mul_gram_root A hs hp b,gram_mul_root A hs hp b] at hh
  simp only [Matrix.neg_apply] at hh
  have hz : rootSign A i*X (.inr (negativeIndex A hs hp i)) (.inr i)=0 := by
    nlinarith [hh]
  exact (mul_eq_zero.mp hz).resolve_left (rootSign_ne_zero A i)

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckGramEntries
