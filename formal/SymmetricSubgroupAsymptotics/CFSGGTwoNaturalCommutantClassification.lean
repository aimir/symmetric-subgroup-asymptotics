import SymmetricSubgroupAsymptotics.CFSGGTwoNaturalCommutant
import Mathlib.Tactic.FinCases

/-! Full all-characteristic natural G2 Lie commutant, certified by
integer combinations of the four actual simple commutation equations.
The selected three-entry pilot was checked first. The elimination uses
only unit pivots, so no division by2 or3 enters the result. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoNaturalCommutantClassification
open CFSGGTwoSerreMatrices CFSGGTwoNaturalCommutant
variable (R : Type*) [CommRing R] (A : Mat R)
    (hpos : ∀i : Fin 2,A*positive R i=positive R i*A)
    (hneg : ∀i : Fin 2,A*negative R i=negative R i*A)
include hpos hneg

private theorem entry_01 : A (pos 0) (pos 1)=0 := by
  have h0 : A (pos 0) (pos 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 0) (pos 0)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0

private theorem entry_02 : A (pos 0) (pos 2)=0 := by
  have h0 : -A (pos 1) (pos 3) - A (pos 1) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 1) (neg 2)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : -A (pos 0) (pos 2) + A (pos 1) (pos 3) + A (pos 1) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 1) (pos 2)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0 - h1

private theorem entry_03 : A (pos 0) (pos 3)=0 := by
  have h0 : -A (pos 0) (pos 3) - A (pos 0) (neg 3) - A (pos 1) (neg 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 0) (neg 2)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : A (pos 0) (pos 3) + A (pos 0) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 0) (pos 2)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h2 : -A (pos 0) (pos 3) - A (pos 1) (neg 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 1) (pos 3)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0 + h1 - h2

private theorem entry_04 : A (pos 0) (neg 0)=0 := by
  have h0 : -A (pos 0) (neg 0)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 0) (neg 1)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0

private theorem entry_05 : A (pos 0) (neg 1)=0 := by
  have h0 : -A (pos 0) (neg 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 0) (neg 2)) (sub_eq_zero.mpr (hneg 1))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0

private theorem entry_06 : A (pos 0) (neg 2)=0 := by
  have h0 : -A (pos 0) (neg 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 0) (pos 3)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0

private theorem entry_10 : A (pos 1) (pos 0)=0 := by
  have h0 : A (pos 1) (pos 0)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 1) (pos 1)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0

private theorem entry_11 : A (pos 1) (pos 1)=A (neg 3) (neg 3)+A (neg 3) (pos 3) := by
  have h0 : A (pos 2) (pos 2) - A (pos 3) (pos 3) - A (neg 3) (pos 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (pos 3)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : A (pos 2) (pos 2) - A (pos 3) (neg 3) - A (neg 3) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (neg 3)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h2 : -A (pos 2) (pos 2) + A (pos 3) (pos 3) + A (pos 3) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 3) (pos 2)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h3 : A (pos 1) (pos 1) - A (pos 2) (pos 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 1) (pos 2)) (sub_eq_zero.mpr (hpos 1))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0 + h1 + h2 + h3

private theorem entry_12 : A (pos 1) (pos 2)=0 := by
  have h0 : A (pos 1) (pos 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 1) (neg 3)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0

private theorem entry_13 : A (pos 1) (pos 3)=0 := by
  have h0 : A (pos 0) (pos 2) - A (pos 1) (pos 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 0) (pos 3)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : -A (pos 1) (pos 3) - A (pos 1) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 1) (neg 2)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h2 : -A (pos 0) (pos 2) + A (pos 1) (pos 3) + A (pos 1) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 1) (pos 2)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0 - h1 - h2

private theorem entry_14 : A (pos 1) (neg 0)=0 := by
  have h0 : -A (pos 0) (neg 1) - A (pos 1) (neg 0)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 0) (neg 0)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : -A (pos 0) (neg 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 0) (neg 2)) (sub_eq_zero.mpr (hneg 1))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0 + h1

private theorem entry_15 : A (pos 1) (neg 1)=0 := by
  have h0 : -A (pos 1) (neg 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 0) (neg 1)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0

private theorem entry_16 : A (pos 1) (neg 2)=0 := by
  have h0 : -A (pos 0) (pos 3) - A (pos 0) (neg 3) - A (pos 1) (neg 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 0) (neg 2)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : A (pos 0) (pos 3) + A (pos 0) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 0) (pos 2)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0 - h1

private theorem entry_17 : A (pos 1) (neg 3)=0 := by
  have h0 : A (pos 0) (pos 2) - A (pos 1) (pos 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 0) (pos 3)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : -A (pos 0) (pos 2) + A (pos 1) (pos 3) + A (pos 1) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 1) (pos 2)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0 + h1

private theorem entry_20 : A (pos 2) (pos 0)=0 := by
  have h0 : A (pos 2) (pos 0) - A (pos 3) (pos 1) - A (neg 3) (pos 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (pos 1)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : A (pos 3) (pos 1) + A (neg 3) (pos 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 2) (pos 1)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0 + h1

private theorem entry_21 : A (pos 2) (pos 1)=0 := by
  have h0 : A (pos 2) (pos 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (pos 0)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0

private theorem entry_22 : A (pos 2) (pos 2)=A (neg 3) (neg 3)+A (neg 3) (pos 3) := by
  have h0 : A (pos 2) (pos 2) - A (pos 3) (pos 3) - A (neg 3) (pos 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (pos 3)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : A (pos 2) (pos 2) - A (pos 3) (neg 3) - A (neg 3) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (neg 3)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h2 : -A (pos 2) (pos 2) + A (pos 3) (pos 3) + A (pos 3) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 3) (pos 2)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0 + h1 + h2

private theorem entry_23 : A (pos 2) (pos 3)=0 := by
  have h0 : -A (pos 2) (pos 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 1) (pos 3)) (sub_eq_zero.mpr (hpos 1))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0

private theorem entry_24 : A (pos 2) (neg 0)=0 := by
  have h0 : -A (pos 2) (neg 0)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (neg 1)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0

private theorem entry_25 : A (pos 2) (neg 1)=0 := by
  have h0 : -A (pos 2) (neg 1) - A (pos 3) (neg 0) - A (neg 3) (neg 0)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (neg 0)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : A (pos 3) (neg 0) + A (neg 3) (neg 0)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 2) (neg 0)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0 - h1

private theorem entry_26 : A (pos 2) (neg 2)=0 := by
  have h0 : -A (pos 2) (neg 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (pos 3)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0

private theorem entry_27 : A (pos 2) (neg 3)=0 := by
  have h0 : A (pos 2) (pos 3) + A (pos 2) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (pos 2)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : -A (pos 2) (pos 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 1) (pos 3)) (sub_eq_zero.mpr (hpos 1))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0 + h1

private theorem entry_31 : A (pos 3) (pos 1)=0 := by
  have h0 : A (pos 2) (pos 0) - A (pos 3) (pos 1) - A (neg 3) (pos 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (pos 1)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : -A (pos 2) (pos 0) + A (pos 3) (pos 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 3) (pos 0)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h2 : A (pos 3) (pos 1) + A (neg 3) (pos 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 2) (pos 1)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0 + h1 + h2

private theorem entry_32 : A (pos 3) (pos 2)=0 := by
  have h0 : A (pos 3) (pos 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 3) (pos 1)) (sub_eq_zero.mpr (hneg 1))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0

private theorem entry_33 : A (pos 3) (pos 3)=A (neg 3) (neg 3) := by
  have h0 : A (pos 2) (pos 2) - A (pos 3) (neg 3) - A (neg 3) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (neg 3)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : -A (pos 2) (pos 2) + A (pos 3) (pos 3) + A (pos 3) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 3) (pos 2)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0 + h1

private theorem entry_34 : A (pos 3) (neg 0)=0 := by
  have h0 : -A (pos 2) (neg 1) - A (pos 3) (neg 0) - A (neg 3) (neg 0)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (neg 0)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : -A (pos 2) (neg 1) - A (pos 3) (neg 0)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 3) (neg 1)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h2 : A (pos 3) (neg 0) + A (neg 3) (neg 0)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 2) (neg 0)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0 - h1 + h2

private theorem entry_35 : A (pos 3) (neg 1)=0 := by
  have h0 : A (neg 2) (neg 0) - A (neg 3) (neg 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 3) (neg 0)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : A (pos 3) (neg 1) - A (neg 2) (neg 0) + A (neg 3) (neg 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 2) (neg 1)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0 + h1

private theorem entry_36 : A (pos 3) (neg 2)=0 := by
  have h0 : -A (pos 2) (pos 3) - A (pos 3) (neg 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 3) (pos 3)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : -A (pos 2) (pos 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 1) (pos 3)) (sub_eq_zero.mpr (hpos 1))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0 + h1

private theorem entry_37 : A (pos 3) (neg 3)=A (neg 3) (pos 3) := by
  have h0 : A (pos 2) (pos 2) - A (pos 3) (pos 3) - A (neg 3) (pos 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (pos 3)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : -A (pos 2) (pos 2) + A (pos 3) (pos 3) + A (pos 3) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 3) (pos 2)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0 + h1

private theorem entry_40 : A (neg 0) (pos 0)=0 := by
  have h0 : A (neg 0) (pos 0)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 1) (pos 0)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0

private theorem entry_41 : A (neg 0) (pos 1)=0 := by
  have h0 : A (neg 0) (pos 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 0) (pos 2)) (sub_eq_zero.mpr (hpos 1))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0

private theorem entry_42 : A (neg 0) (pos 2)=0 := by
  have h0 : A (neg 0) (pos 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 0) (neg 3)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0

private theorem entry_43 : A (neg 0) (pos 3)=0 := by
  have h0 : -A (neg 0) (pos 3) - A (neg 0) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 0) (neg 2)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : A (neg 0) (pos 3) + A (neg 1) (pos 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 1) (pos 3)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h2 : A (neg 0) (pos 3) + A (neg 0) (neg 3) + A (neg 1) (pos 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 0) (pos 2)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0 + h1 - h2

private theorem entry_44 : A (neg 0) (neg 0)=A (neg 3) (neg 3)+A (neg 3) (pos 3) := by
  have h0 : A (pos 2) (pos 2) - A (pos 3) (pos 3) - A (neg 3) (pos 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (pos 3)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : A (pos 2) (pos 2) - A (pos 3) (neg 3) - A (neg 3) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (neg 3)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h2 : -A (pos 3) (pos 3) - A (pos 3) (neg 3) + A (neg 2) (neg 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 3) (neg 2)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h3 : A (neg 0) (neg 0) - A (neg 1) (neg 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 1) (neg 0)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h4 : -A (pos 2) (pos 2) + A (pos 3) (pos 3) + A (pos 3) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 3) (pos 2)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h5 : A (neg 1) (neg 1) - A (neg 2) (neg 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 2) (neg 1)) (sub_eq_zero.mpr (hpos 1))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0 + h1 + h2 + h3 + 2 * h4 + h5

private theorem entry_45 : A (neg 0) (neg 1)=0 := by
  have h0 : A (neg 0) (neg 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 1) (neg 1)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0

private theorem entry_46 : A (neg 0) (neg 2)=0 := by
  have h0 : A (neg 0) (neg 2) - A (neg 1) (pos 3) - A (neg 1) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 1) (neg 2)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : -A (neg 0) (neg 2) + A (neg 1) (pos 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 0) (pos 3)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h2 : -A (neg 0) (neg 2) + A (neg 1) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 0) (neg 3)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0 - h1 - h2

private theorem entry_47 : A (neg 0) (neg 3)=0 := by
  have h0 : A (neg 0) (pos 3) + A (neg 1) (pos 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 1) (pos 3)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : A (neg 0) (pos 3) + A (neg 0) (neg 3) + A (neg 1) (pos 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 0) (pos 2)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0 + h1

private theorem entry_50 : A (neg 1) (pos 0)=0 := by
  have h0 : A (neg 0) (pos 1) + A (neg 1) (pos 0)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 1) (pos 1)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : A (neg 0) (pos 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 0) (pos 2)) (sub_eq_zero.mpr (hpos 1))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0 - h1

private theorem entry_51 : A (neg 1) (pos 1)=0 := by
  have h0 : A (neg 1) (pos 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 0) (pos 1)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0

private theorem entry_52 : A (neg 1) (pos 2)=0 := by
  have h0 : -A (neg 0) (pos 3) - A (neg 0) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 0) (neg 2)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : A (neg 0) (pos 3) + A (neg 0) (neg 3) + A (neg 1) (pos 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 0) (pos 2)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0 + h1

private theorem entry_53 : A (neg 1) (pos 3)=0 := by
  have h0 : A (neg 0) (neg 2) - A (neg 1) (pos 3) - A (neg 1) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 1) (neg 2)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : -A (neg 0) (neg 2) + A (neg 1) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 0) (neg 3)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0 - h1

private theorem entry_54 : A (neg 1) (neg 0)=0 := by
  have h0 : A (neg 1) (neg 0)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 0) (neg 0)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0

private theorem entry_55 : A (neg 1) (neg 1)=A (neg 3) (neg 3)+A (neg 3) (pos 3) := by
  have h0 : A (pos 2) (pos 2) - A (pos 3) (pos 3) - A (neg 3) (pos 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (pos 3)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : A (pos 2) (pos 2) - A (pos 3) (neg 3) - A (neg 3) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (neg 3)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h2 : -A (pos 3) (pos 3) - A (pos 3) (neg 3) + A (neg 2) (neg 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 3) (neg 2)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h3 : -A (pos 2) (pos 2) + A (pos 3) (pos 3) + A (pos 3) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 3) (pos 2)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h4 : A (neg 1) (neg 1) - A (neg 2) (neg 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 2) (neg 1)) (sub_eq_zero.mpr (hpos 1))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0 + h1 + h2 + 2 * h3 + h4

private theorem entry_56 : A (neg 1) (neg 2)=0 := by
  have h0 : A (neg 1) (neg 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 0) (neg 2)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0

private theorem entry_57 : A (neg 1) (neg 3)=0 := by
  have h0 : A (neg 0) (neg 2) - A (neg 1) (pos 3) - A (neg 1) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 1) (neg 2)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : -A (neg 0) (neg 2) + A (neg 1) (pos 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 0) (pos 3)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0 - h1

private theorem entry_60 : A (neg 2) (pos 0)=0 := by
  have h0 : A (neg 2) (pos 0)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 3) (pos 0)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0

private theorem entry_61 : A (neg 2) (pos 1)=0 := by
  have h0 : -A (pos 3) (pos 0) - A (neg 3) (pos 0)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (pos 0)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : A (pos 3) (pos 0) + A (neg 2) (pos 1) + A (neg 3) (pos 0)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 2) (pos 0)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0 + h1

private theorem entry_62 : A (neg 2) (pos 2)=0 := by
  have h0 : A (neg 2) (pos 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 3) (pos 2)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0

private theorem entry_63 : A (neg 2) (pos 3)=0 := by
  have h0 : A (pos 3) (pos 2) + A (neg 2) (pos 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 3) (pos 3)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : A (pos 3) (pos 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 3) (pos 1)) (sub_eq_zero.mpr (hneg 1))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0 - h1

private theorem entry_64 : A (neg 2) (neg 0)=0 := by
  have h0 : -A (pos 3) (neg 1) - A (neg 3) (neg 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (neg 1)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : A (pos 3) (neg 1) - A (neg 2) (neg 0) + A (neg 3) (neg 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 2) (neg 1)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0 - h1

private theorem entry_65 : A (neg 2) (neg 1)=0 := by
  have h0 : A (neg 2) (neg 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 3) (neg 1)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0

private theorem entry_66 : A (neg 2) (neg 2)=A (neg 3) (neg 3)+A (neg 3) (pos 3) := by
  have h0 : A (pos 2) (pos 2) - A (pos 3) (pos 3) - A (neg 3) (pos 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (pos 3)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : A (pos 2) (pos 2) - A (pos 3) (neg 3) - A (neg 3) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (neg 3)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h2 : -A (pos 3) (pos 3) - A (pos 3) (neg 3) + A (neg 2) (neg 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 3) (neg 2)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h3 : -A (pos 2) (pos 2) + A (pos 3) (pos 3) + A (pos 3) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 3) (pos 2)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0 + h1 + h2 + 2 * h3

private theorem entry_67 : A (neg 2) (neg 3)=0 := by
  have h0 : A (pos 3) (pos 2) + A (neg 2) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 3) (neg 3)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : A (pos 3) (pos 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 3) (pos 1)) (sub_eq_zero.mpr (hneg 1))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination h0 - h1

private theorem entry_70 : A (neg 3) (pos 0)=0 := by
  have h0 : -A (pos 3) (pos 0) - A (neg 3) (pos 0)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (pos 0)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : A (neg 2) (pos 1) + A (neg 3) (pos 0)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 3) (pos 1)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h2 : A (pos 3) (pos 0) + A (neg 2) (pos 1) + A (neg 3) (pos 0)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 2) (pos 0)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0 + h1 - h2

private theorem entry_71 : A (neg 3) (pos 1)=0 := by
  have h0 : A (pos 2) (pos 0) - A (pos 3) (pos 1) - A (neg 3) (pos 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (pos 1)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : -A (pos 2) (pos 0) + A (pos 3) (pos 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 3) (pos 0)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0 - h1

private theorem entry_72 : A (neg 3) (pos 2)=0 := by
  have h0 : A (pos 3) (pos 2) + A (neg 2) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 3) (neg 3)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : A (neg 2) (neg 3) + A (neg 3) (pos 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 3) (neg 3)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h2 : A (pos 3) (pos 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 3) (pos 1)) (sub_eq_zero.mpr (hneg 1))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0 + h1 + h2

private theorem entry_74 : A (neg 3) (neg 0)=0 := by
  have h0 : -A (pos 2) (neg 1) - A (pos 3) (neg 0) - A (neg 3) (neg 0)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (neg 0)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : -A (pos 2) (neg 1) - A (pos 3) (neg 0)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 3) (neg 1)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0 + h1

private theorem entry_75 : A (neg 3) (neg 1)=0 := by
  have h0 : -A (pos 3) (neg 1) - A (neg 3) (neg 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (neg 1)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : A (neg 2) (neg 0) - A (neg 3) (neg 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 3) (neg 0)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h2 : A (pos 3) (neg 1) - A (neg 2) (neg 0) + A (neg 3) (neg 1)=0 := by
    have raw := congrArg (fun M : Mat R=>M (neg 2) (neg 1)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0 - h1 - h2

private theorem entry_76 : A (neg 3) (neg 2)=0 := by
  have h0 : -A (pos 2) (pos 3) - A (pos 2) (neg 3) - A (pos 3) (neg 2) - A (neg 3) (neg 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (neg 2)) (sub_eq_zero.mpr (hpos 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h1 : A (pos 2) (pos 3) + A (pos 2) (neg 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 2) (pos 2)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h2 : -A (pos 2) (pos 3) - A (pos 3) (neg 2)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 3) (pos 3)) (sub_eq_zero.mpr (hneg 0))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  have h3 : -A (pos 2) (pos 3)=0 := by
    have raw := congrArg (fun M : Mat R=>M (pos 1) (pos 3)) (sub_eq_zero.mpr (hpos 1))
    convert raw using 1
    simp only [Matrix.sub_apply,negative,positive_zero_explicit,positive_one_explicit,
      Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_single,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.add_apply,Matrix.sub_apply]
    norm_num [Matrix.mul_apply,Matrix.single_apply,pos,neg,Fin.ext_iff,
      Fintype.sum_sum_type,Fin.sum_univ_succ,Sum.inl_ne_inr,Sum.inr_ne_inl] <;> ring
  linear_combination -h0 - h1 + h2 - h3

omit A hpos hneg in
def axisSwap : Mat R := fun i j=>if j=Equiv.swap (pos 3) (neg 3) i then 1 else 0

theorem commutant_eq : ∃a b : R,A=a • (1:Mat R)+b • axisSwap R := by
  refine ⟨A (neg 3) (neg 3),A (neg 3) (pos 3),?_⟩
  apply Matrix.ext
  intro i j
  rcases i with i|i <;> rcases j with j|j <;> fin_cases i <;> fin_cases j
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using diagonal_zero R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_01 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_02 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_03 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_10 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_11 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_12 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_13 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_20 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_21 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_22 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_23 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using positive_last_positive_zero R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_31 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_32 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_33 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_04 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_05 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_06 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using positive_zero_negative_last R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_14 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_15 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_16 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_17 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_24 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_25 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_26 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_27 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_34 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_35 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_36 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_37 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_40 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_41 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_42 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_43 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_50 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_51 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_52 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_53 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_60 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_61 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_62 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_63 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_70 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_71 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_72 R A hpos hneg
  · simp [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff]
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_44 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_45 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_46 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_47 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_54 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_55 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_56 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_57 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_64 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_65 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_66 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_67 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_74 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_75 R A hpos hneg
  · simpa [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff] using entry_76 R A hpos hneg
  · simp [axisSwap,pos,neg,Equiv.swap_apply_def,Fin.ext_iff]

end SymmetricSubgroupAsymptotics.CFSGGTwoNaturalCommutantClassification
