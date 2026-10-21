import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreRepresentation
import Mathlib.Algebra.Lie.SkewAdjoint

/-! The SAME original rational B representation preserves an explicit
orthogonal form. This proves the missing fourth root-conjugation
coefficient vanishes on its actual image, rather than on all matrices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
open CFSG.Models.Chevalley

/-- Hyperbolic pairs have Gram entry two; the middle coordinate has entry one. -/
def gram (R : Type*) [CommRing R] (r : ℕ) : Mat R r := fun a b=>
  match a,b with
  | .inl (.inl a),.inl (.inr b)=>if a=b then 2 else 0
  | .inl (.inr a),.inl (.inl b)=>if a=b then 2 else 0
  | .inr _,.inr _=>1
  | _,_=>0

theorem positive_mem_orthogonal (R : Type*) [CommRing R] (r : ℕ) (i : Fin r) :
    positive R r i∈skewAdjointMatricesLieSubalgebra (gram R r) := by
  rw [mem_skewAdjointMatricesLieSubalgebra,mem_skewAdjointMatricesSubmodule]
  change (positive R r i).transpose*gram R r=gram R r*(-positive R r i)
  by_cases hi : i.val+1<r
  all_goals
    simp only [positive,hi,↓reduceDIte,Matrix.transpose_sub,Matrix.transpose_single,
      sub_mul,mul_sub,mul_neg]
    ext a b
    rcases a with (a|a)|a <;> rcases b with (b|b)|b <;>
      simp [gram,pos,neg,middle,Matrix.mul_apply,Matrix.single,Fintype.sum_sum_type,ite_and,eq_comm] <;>
      (try split_ifs) <;> ring

theorem negative_mem_orthogonal (R : Type*) [CommRing R] (r : ℕ) (i : Fin r) :
    negative R r i∈skewAdjointMatricesLieSubalgebra (gram R r) := by
  rw [mem_skewAdjointMatricesLieSubalgebra,mem_skewAdjointMatricesSubmodule]
  change (negative R r i).transpose*gram R r=gram R r*(-negative R r i)
  by_cases hi : i.val+1<r
  all_goals
    simp only [negative,hi,↓reduceDIte,Matrix.transpose_sub,Matrix.transpose_single,
      sub_mul,mul_sub,mul_neg]
    ext a b
    rcases a with (a|a)|a <;> rcases b with (b|b)|b <;>
      simp [gram,pos,neg,middle,Matrix.mul_apply,Matrix.single,Fintype.sum_sum_type,ite_and,eq_comm] <;>
      (try split_ifs) <;> ring

theorem rational_image_mem_orthogonal (r : ℕ) (x : RationalLie (CartanMatrix.B r).transpose) :
    rationalOrthogonalRepresentation r x∈skewAdjointMatricesLieSubalgebra (gram ℚ r) := by
  let S := (skewAdjointMatricesLieSubalgebra (gram ℚ r)).comap (rationalOrthogonalRepresentation r)
  have hle : LieSubalgebra.lieSpan ℚ _ (Set.range (generator (CartanMatrix.B r).transpose))≤S := by
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨g,rfl⟩
    change rationalOrthogonalRepresentation r (generator (CartanMatrix.B r).transpose g)∈
      skewAdjointMatricesLieSubalgebra (gram ℚ r)
    cases g with
    | H i=>
      rw [rationalOrthogonalRepresentation_H]
      exact (skewAdjointMatricesLieSubalgebra (gram ℚ r)).lie_mem
        (positive_mem_orthogonal ℚ r i) (negative_mem_orthogonal ℚ r i)
    | E i=>rw [rationalOrthogonalRepresentation_E];exact positive_mem_orthogonal ℚ r i
    | F i=>rw [rationalOrthogonalRepresentation_F];exact negative_mem_orthogonal ℚ r i
  rw [CFSGSerreLocalNilpotence.generator_lieSpan_eq_top] at hle
  exact hle (LieSubalgebra.mem_top x)

theorem orthogonal_opposite_entries_zero (r : ℕ) (X : Mat ℚ r)
    (hX : X∈skewAdjointMatricesLieSubalgebra (gram ℚ r)) (i : Fin r) :
    X (neg r i) (pos r i)=0 ∧ X (pos r i) (neg r i)=0 := by
  rw [mem_skewAdjointMatricesLieSubalgebra,mem_skewAdjointMatricesSubmodule] at hX
  change X.transpose*gram ℚ r=gram ℚ r*(-X) at hX
  have hp := congrArg (fun M : Mat ℚ r=>M (pos r i) (pos r i)) hX
  have hn := congrArg (fun M : Mat ℚ r=>M (neg r i) (neg r i)) hX
  simp [gram,pos,neg,middle,Matrix.mul_apply,Fintype.sum_sum_type,Matrix.transpose_apply] at hp hn
  constructor <;> linarith

theorem rational_image_fourth_coefficient_zero (r : ℕ)
    (x : RationalLie (CartanMatrix.B r).transpose) (neg : Bool) (i : Fin r) :
    (if neg then negativeSecond ℚ r i else positiveSecond ℚ r i)*
      rationalOrthogonalRepresentation r x*
      (if neg then negativeSecond ℚ r i else positiveSecond ℚ r i)=0 := by
  have hz := orthogonal_opposite_entries_zero r _ (rational_image_mem_orthogonal r x) i
  by_cases hi : i.val+1<r
  · cases neg <;> simp [positiveSecond,negativeSecond,hi]
  · cases neg
    · simp only [Bool.false_eq_true,if_false,positiveSecond,if_neg hi,Matrix.single_mul_mul_single,
        hz.1,mul_zero,zero_mul,Matrix.single_zero]
    · simp only [if_true,negativeSecond,if_neg hi,Matrix.single_mul_mul_single,
        hz.2,mul_zero,zero_mul,Matrix.single_zero]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
