import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
import Mathlib.Algebra.Lie.SkewAdjoint
import Mathlib.Tactic.Ring

/-! The literal natural D root matrices preserve the hyperbolic form.
This shared matrix identity imposes no source faithfulness assumption. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices

 def gram (R : Type*) [CommRing R] (r : ℕ) : Mat R r := fun a b=>
  match a,b with
  | .inl a,.inr b=>if a=b then 1 else 0
  | .inr a,.inl b=>if a=b then 1 else 0
  | _,_=>0

 theorem positive_mem_orthogonal (R : Type*) [CommRing R] (r : ℕ) (i : Fin r) :
    positive R r i∈skewAdjointMatricesLieSubalgebra (gram R r) := by
  rw [mem_skewAdjointMatricesLieSubalgebra,mem_skewAdjointMatricesSubmodule]
  change (positive R r i).transpose*gram R r=gram R r*(-positive R r i)
  by_cases hi : i.val+1 < r
  all_goals
    simp only [positive,hi,↓reduceDIte,Matrix.transpose_sub,Matrix.transpose_single,
      sub_mul,mul_sub,mul_neg]
    ext a b
    rcases a with a|a <;> rcases b with b|b <;>
      simp [gram,Matrix.mul_apply,Matrix.single,Fintype.sum_sum_type,ite_and,eq_comm] <;>
      (try split_ifs) <;> ring

 theorem negative_mem_orthogonal (R : Type*) [CommRing R] (r : ℕ) (i : Fin r) :
    negative R r i∈skewAdjointMatricesLieSubalgebra (gram R r) := by
  rw [mem_skewAdjointMatricesLieSubalgebra,mem_skewAdjointMatricesSubmodule]
  change (negative R r i).transpose*gram R r=gram R r*(-negative R r i)
  by_cases hi : i.val+1 < r
  all_goals
    simp only [negative,positive,hi,↓reduceDIte,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.transpose_transpose,sub_mul,mul_sub,mul_neg]
    ext a b
    rcases a with a|a <;> rcases b with b|b <;>
      simp [gram,Matrix.mul_apply,Matrix.single,Fintype.sum_sum_type,ite_and,eq_comm] <;>
      (try split_ifs) <;> ring

 theorem orthogonal_opposite_entries_zero (r : ℕ) (X : Mat ℚ r)
    (hX : X∈skewAdjointMatricesLieSubalgebra (gram ℚ r)) (i : Fin r) :
    X (Sum.inr i) (Sum.inl i)=0 ∧ X (Sum.inl i) (Sum.inr i)=0 := by
  rw [mem_skewAdjointMatricesLieSubalgebra,mem_skewAdjointMatricesSubmodule] at hX
  change X.transpose*gram ℚ r=gram ℚ r*(-X) at hX
  have hp := congrArg (fun M : Mat ℚ r=>M (Sum.inl i) (Sum.inl i)) hX
  have hn := congrArg (fun M : Mat ℚ r=>M (Sum.inr i) (Sum.inr i)) hX
  simp [gram,Matrix.mul_apply,Fintype.sum_sum_type,Matrix.transpose_apply] at hp hn
  constructor <;> linarith

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
