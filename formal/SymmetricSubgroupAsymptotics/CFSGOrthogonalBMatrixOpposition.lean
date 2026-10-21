import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveSupport
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! The actual interchange of positive and negative coordinate labels
sends E_i to -F_i, including both terminal coefficients. This transfers
matrix product identities without incorrectly transposing the short root. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

def oppositionIndex : Index r≃Index r :=
  Equiv.sumCongr (Equiv.sumComm (Fin r) (Fin r)) (Equiv.refl Unit)

def opposition : Mat R r≃ₐ[R]Mat R r := Matrix.reindexAlgEquiv R R (oppositionIndex r)

theorem opposition_positive (i : Fin r) : opposition R r (positive R r i)= -negative R r i := by
  by_cases hi : i.val+1<r
  all_goals
    ext a b
    rcases a with (a|a)|a <;> rcases b with (b|b)|b <;>
      simp [opposition,oppositionIndex,positive,negative,hi,pos,neg,middle,
        Matrix.reindexAlgEquiv_apply,Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.single] <;> abel

theorem opposition_positiveSecond (i : Fin r) :
    opposition R r (positiveSecond R r i)=negativeSecond R r i := by
  by_cases hi : i.val+1<r
  all_goals
    ext a b
    rcases a with (a|a)|a <;> rcases b with (b|b)|b <;>
      simp [opposition,oppositionIndex,positiveSecond,negativeSecond,hi,pos,neg,middle,
        Matrix.reindexAlgEquiv_apply,Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.single]

theorem negative_sandwich (i j : Fin r) : negative R r i*negative R r j*negative R r i=0 := by
  have hh := congrArg (opposition R r) (positive_sandwich R r i j)
  simpa only [map_mul,opposition_positive,map_zero,neg_mul,mul_neg,neg_neg,neg_eq_zero] using hh

theorem negative_mul_other_second (i j : Fin r) :
    negative R r i*negative R r j*negativeSecond R r i=0 := by
  have hh := congrArg (opposition R r) (positive_mul_other_second R r i j)
  simpa only [map_mul,opposition_positive,opposition_positiveSecond,map_zero,
    neg_mul,mul_neg,neg_neg] using hh

theorem second_mul_other_negative (i j : Fin r) :
    negativeSecond R r i*negative R r j*negative R r i=0 := by
  have hh := congrArg (opposition R r) (second_mul_other_positive R r i j)
  simpa only [map_mul,opposition_positive,opposition_positiveSecond,map_zero,
    neg_mul,mul_neg,neg_neg] using hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
