import SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-! Selected sparse-coordinate pilots for the actual natural G2 Lie
commutant. Certificates use only integral linear combinations of the
four literal simple commutation relations, without division by2 or3.
The full commutant classification is not asserted by this pilot. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoNaturalCommutant
open CFSGGTwoSerreMatrices
variable (R : Type*) [CommRing R] (A : Mat R)
    (hpos : ∀i : Fin 2,A*positive R i=positive R i*A)
    (hneg : ∀i : Fin 2,A*negative R i=negative R i*A)
include hpos hneg

theorem diagonal_zero : A (pos 0) (pos 0)=A (neg 3) (neg 3)+A (neg 3) (pos 3) := by
  have h0 := congrArg (fun M : Mat R=>M (pos 0) (pos 1)) (hpos 0)
  simp only [negative,positive_zero_explicit,positive_one_explicit,
    Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
    Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.add_apply,Matrix.sub_apply] at h0
  norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
    Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] at h0
  have h1 := congrArg (fun M : Mat R=>M (pos 2) (pos 3)) (hpos 0)
  simp only [negative,positive_zero_explicit,positive_one_explicit,
    Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
    Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.add_apply,Matrix.sub_apply] at h1
  norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
    Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] at h1
  have h2 := congrArg (fun M : Mat R=>M (pos 2) (neg 3)) (hpos 0)
  simp only [negative,positive_zero_explicit,positive_one_explicit,
    Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
    Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.add_apply,Matrix.sub_apply] at h2
  norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
    Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] at h2
  have h3 := congrArg (fun M : Mat R=>M (pos 3) (pos 2)) (hneg 0)
  simp only [negative,positive_zero_explicit,positive_one_explicit,
    Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
    Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.add_apply,Matrix.sub_apply] at h3
  norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
    Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] at h3
  have h4 := congrArg (fun M : Mat R=>M (pos 1) (pos 2)) (hpos 1)
  simp only [negative,positive_zero_explicit,positive_one_explicit,
    Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
    Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.add_apply,Matrix.sub_apply] at h4
  norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
    Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] at h4
  linear_combination h0 + h1 + h2 + h3 + h4

theorem positive_zero_negative_last : A (pos 0) (neg 3)=0 := by
  have h0 := congrArg (fun M : Mat R=>M (pos 0) (neg 2)) (hpos 0)
  simp only [negative,positive_zero_explicit,positive_one_explicit,
    Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
    Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.add_apply,Matrix.sub_apply] at h0
  norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
    Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] at h0
  have h1 := congrArg (fun M : Mat R=>M (pos 1) (pos 3)) (hneg 0)
  simp only [negative,positive_zero_explicit,positive_one_explicit,
    Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
    Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.add_apply,Matrix.sub_apply] at h1
  norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
    Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] at h1
  linear_combination -h0 + h1

theorem positive_last_positive_zero : A (pos 3) (pos 0)=0 := by
  have h0 := congrArg (fun M : Mat R=>M (neg 3) (pos 1)) (hpos 0)
  simp only [negative,positive_zero_explicit,positive_one_explicit,
    Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
    Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.add_apply,Matrix.sub_apply] at h0
  norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
    Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] at h0
  have h1 := congrArg (fun M : Mat R=>M (neg 2) (pos 0)) (hneg 0)
  simp only [negative,positive_zero_explicit,positive_one_explicit,
    Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
    Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.add_apply,Matrix.sub_apply] at h1
  norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
    Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] at h1
  linear_combination -h0 + h1

end SymmetricSubgroupAsymptotics.CFSGGTwoNaturalCommutant
