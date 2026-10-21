import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Actual elementary matrices for the literal special linear group.
The identities hold over arbitrary fields and in arbitrary dimension;
no identification with a Chevalley presentation is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTypeAElementaryMatrices
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n] {F : Type*} [Field F]

abbrev SL := Matrix.SpecialLinearGroup n F

def elementary {i j : n} (hij : i≠j) (a : F) : SL (n:=n) (F:=F) :=
  ⟨Matrix.transvection i j a,Matrix.det_transvection_of_ne i j hij a⟩

@[simp] theorem elementary_coe {i j : n} (hij : i≠j) (a : F) :
    (elementary hij a).val=Matrix.transvection i j a := rfl

@[simp] theorem elementary_zero {i j : n} (hij : i≠j) :
    elementary (F:=F) hij 0=1 := by
  apply Subtype.ext
  exact Matrix.transvection_zero i j

theorem elementary_add {i j : n} (hij : i≠j) (a b : F) :
    elementary hij (a+b)=elementary hij a*elementary hij b := by
  apply Subtype.ext
  exact (Matrix.transvection_mul_transvection_same i j hij a b).symm

@[simp] theorem elementary_inv {i j : n} (hij : i≠j) (a : F) :
    (elementary hij a)⁻¹=elementary hij (-a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [←elementary_add,add_neg_cancel,elementary_zero]

/-- The Steinberg commutator relation inside actual determinant-one
matrices, with the original coordinate indices. -/
theorem elementary_commutator {i j k : n} (hij : i≠j) (hjk : j≠k)
    (hik : i≠k) (a b : F) :
    ⁅elementary hij a,elementary hjk b⁆=elementary hik (a*b) := by
  rw [commutatorElement_def,elementary_inv,elementary_inv]
  apply Subtype.ext
  change Matrix.transvection i j a*Matrix.transvection j k b*
    Matrix.transvection i j (-a)*Matrix.transvection j k (-b)=Matrix.transvection i k (a*b)
  simp only [Matrix.transvection,Matrix.add_mul,Matrix.mul_add,
    Matrix.one_mul,Matrix.mul_one,Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hij),
    Matrix.single_mul_single_of_ne _ _ _ _ hjk,
    Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hjk),
    Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hik)]
  ext r s
  by_cases hri : r=i <;> by_cases hrj : r=j <;>
    by_cases hsj : s=j <;> by_cases hsk : s=k <;>
    simp_all [Matrix.single_apply,Matrix.one_apply,Ne.symm hij,Ne.symm hjk,Ne.symm hik] <;>
    split_ifs <;> simp_all <;> ring

/-- A two-coordinate diagonal factor is a product of four actual
transvections. This removes the diagonal factors in Gaussian elimination. -/
theorem diagonal_pair {i j : n} (hij : i≠j) (a : F) (ha : a≠0) :
    Matrix.transvection i j (a-1)*Matrix.transvection j i 1*
      Matrix.transvection i j (a⁻¹-1)*Matrix.transvection j i (-a)=
      Matrix.diagonal (fun k => if k=i then a else if k=j then a⁻¹ else 1) := by
  simp only [Matrix.transvection,Matrix.add_mul,Matrix.mul_add,
    Matrix.one_mul,Matrix.mul_one,Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ hij,
    Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hij)]
  ext r s
  by_cases hri : r=i <;> by_cases hrj : r=j <;>
    by_cases hsi : s=i <;> by_cases hsj : s=j <;>
    simp_all [Matrix.single_apply,Matrix.one_apply,Matrix.diagonal,Ne.symm hij] <;>
    (try split_ifs) <;> (try simp_all) <;> field_simp [ha] <;> ring

end SymmetricSubgroupAsymptotics.CFSGTypeAElementaryMatrices
