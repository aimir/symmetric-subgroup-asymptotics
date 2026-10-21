import SymmetricSubgroupAsymptotics.CFSGTypeAElementaryMatrices
import Mathlib.LinearAlgebra.Matrix.Block

/-! Literal upper-triangular and upper-unitriangular subgroups of SL_n.
All conditions are on the entries of the original determinant-one matrix,
over an arbitrary field and in every finite dimension. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGUpperUnitriangular
open Matrix

abbrev SL (F : Type*) [Field F] (n : ℕ) := Matrix.SpecialLinearGroup (Fin n) F

theorem upper_diag_mul {F : Type*} [Field F] {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) F}
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  change (∑ k, A i k * B k i) = _
  refine Finset.sum_eq_single i ?_ ?_
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hk | hk
    · rw [hA hk, zero_mul]
    · rw [hB hk, mul_zero]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem upper_inverse {F : Type*} [Field F] {n : ℕ}
    (A : SL F n) (hA : A.val.BlockTriangular id) :
    (A⁻¹).val.BlockTriangular id := by
  letI upperUnitriangular_invertible : Invertible A.val :=
    Matrix.invertibleOfIsUnitDet A.val (by rw [A.property]; exact isUnit_one)
  have hi : A.val⁻¹ = (A⁻¹).val :=
    Matrix.inv_eq_left_inv (show (A⁻¹).val * A.val = 1 from
      congrArg (fun g : SL F n => g.val) (inv_mul_cancel A))
  have h := Matrix.blockTriangular_inv_of_blockTriangular hA
  rw [hi] at h
  exact h

def borel (F : Type*) [Field F] (n : ℕ) : Subgroup (SL F n) where
  carrier := {A | A.val.BlockTriangular id}
  one_mem' := Matrix.blockTriangular_one
  mul_mem' := fun hA hB => hA.mul hB
  inv_mem' := fun hA => upper_inverse _ hA

@[simp] theorem mem_borel {F : Type*} [Field F] {n : ℕ} (A : SL F n) :
    A ∈ borel F n ↔ A.val.BlockTriangular id := Iff.rfl

def upperUnitriangular (F : Type*) [Field F] (n : ℕ) : Subgroup (SL F n) where
  carrier := {A | A.val.BlockTriangular id ∧ ∀ i, A.val i i = 1}
  one_mem' := ⟨Matrix.blockTriangular_one, fun i => Matrix.one_apply_eq i⟩
  mul_mem' := by
    intro A B hA hB
    refine ⟨hA.1.mul hB.1, fun i => ?_⟩
    change (A.val * B.val) i i = 1
    rw [upper_diag_mul hA.1 hB.1, hA.2 i, hB.2 i, one_mul]
  inv_mem' := by
    intro A hA
    have hi := upper_inverse A hA.1
    refine ⟨hi, fun i => ?_⟩
    have h := congrArg (fun g : SL F n => g.val i i) (inv_mul_cancel A)
    change ((A⁻¹).val * A.val) i i = (1 : Matrix (Fin n) (Fin n) F) i i at h
    rw [upper_diag_mul hi hA.1, hA.2 i, mul_one, Matrix.one_apply_eq] at h
    exact h

@[simp] theorem mem_upperUnitriangular {F : Type*} [Field F] {n : ℕ} (A : SL F n) :
    A ∈ upperUnitriangular F n ↔ A.val.BlockTriangular id ∧ ∀ i, A.val i i = 1 := Iff.rfl

theorem upperUnitriangular_le_borel (F : Type*) [Field F] (n : ℕ) :
    upperUnitriangular F n ≤ borel F n := fun _ h => h.1

theorem elementary_mem_upperUnitriangular {F : Type*} [Field F] {n : ℕ}
    {i j : Fin n} (hij : i < j) (a : F) :
    CFSGTypeAElementaryMatrices.elementary (ne_of_lt hij) a ∈ upperUnitriangular F n := by
  refine ⟨Matrix.blockTriangular_transvection hij.le a, ?_⟩
  intro k
  change Matrix.transvection i j a k k = 1
  by_cases hki : k = i
  · subst k
    simp [Matrix.transvection, Matrix.single_apply, ne_of_lt hij, Ne.symm (ne_of_lt hij)]
  · simp [Matrix.transvection, Matrix.single_apply, hki, Ne.symm hki]

end SymmetricSubgroupAsymptotics.CFSGUpperUnitriangular
