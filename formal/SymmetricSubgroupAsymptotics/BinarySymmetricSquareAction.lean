import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-! Literal symmetric binary matrices and their actual GL2 congruence
action, over every field. No classical-group recognition is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.BinarySymmetricSquareAction

variable {K : Type*} [Field K]
abbrev GeneralLinear := (Matrix (Fin 2) (Fin 2) K)ˣ

def symmetricSubmodule : Submodule K (Matrix (Fin 2) (Fin 2) K) where
  carrier := {S | S.IsSymm}
  zero_mem' := Matrix.isSymm_zero
  add_mem' := fun hS hT => hS.add hT
  smul_mem' := fun r _ hS => hS.smul r

abbrev Space := symmetricSubmodule (K := K)

/-- Coordinates are the two diagonal entries and the single shared
 off-diagonal entry; no division by two is involved. -/
def coordinates : (Fin 3 → K) ≃ₗ[K] Space (K := K) where
  toFun s := ⟨!![s 0, s 1; s 1, s 2], by
    apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl⟩
  invFun S := ![S.val 0 0, S.val 0 1, S.val 1 1]
  left_inv s := by
    funext i
    fin_cases i <;> rfl
  right_inv S := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · change S.val 0 1 = S.val 1 0
      exact S.property.apply 1 0
    · rfl
  map_add' s t := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_smul' r s := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem coordinates_val (s : Fin 3 → K) :
    (coordinates s).val = !![s 0, s 1; s 1, s 2] := rfl

/-- The congruence map is defined by actual multiplication of matrices. -/
def congruenceLinearMap (A : GeneralLinear (K := K)) :
    Space (K := K) →ₗ[K] Space (K := K) where
  toFun S := ⟨A.val * S.val * A.val.transpose, by
    change (A.val * S.val * A.val.transpose).transpose = _
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      S.property, Matrix.mul_assoc]⟩
  map_add' S T := by
    apply Subtype.ext
    change A.val * (S.val + T.val) * A.val.transpose =
      A.val * S.val * A.val.transpose + A.val * T.val * A.val.transpose
    rw [mul_add, add_mul]
  map_smul' r S := by
    apply Subtype.ext
    change A.val * (r • S.val) * A.val.transpose =
      r • (A.val * S.val * A.val.transpose)
    rw [mul_smul_comm, smul_mul_assoc]

@[simp] theorem congruenceLinearMap_one (S : Space (K := K)) :
    congruenceLinearMap 1 S = S := by
  apply Subtype.ext
  change (1 : Matrix (Fin 2) (Fin 2) K) * S.val *
    (1 : Matrix (Fin 2) (Fin 2) K).transpose = S.val
  rw [Matrix.transpose_one, one_mul, mul_one]

theorem congruenceLinearMap_mul (A B : GeneralLinear (K := K)) (S : Space (K := K)) :
    congruenceLinearMap (A * B) S =
      congruenceLinearMap A (congruenceLinearMap B S) := by
  apply Subtype.ext
  change (A.val * B.val) * S.val * (A.val * B.val).transpose =
    A.val * (B.val * S.val * B.val.transpose) * A.val.transpose
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- The actual congruence maps form a representation by linear equivalences. -/
def congruence : GeneralLinear (K := K) →* Space (K := K) ≃ₗ[K] Space (K := K) where
  toFun A :=
    { congruenceLinearMap A with
      invFun := congruenceLinearMap A⁻¹
      left_inv := by
        intro S
        change congruenceLinearMap A⁻¹ (congruenceLinearMap A S) = S
        rw [← congruenceLinearMap_mul, inv_mul_cancel, congruenceLinearMap_one]
      right_inv := by
        intro S
        change congruenceLinearMap A (congruenceLinearMap A⁻¹ S) = S
        rw [← congruenceLinearMap_mul, mul_inv_cancel, congruenceLinearMap_one] }
  map_one' := by
    apply LinearEquiv.ext
    intro S
    exact congruenceLinearMap_one S
  map_mul' A B := by
    apply LinearEquiv.ext
    intro S
    exact congruenceLinearMap_mul A B S

end SymmetricSubgroupAsymptotics.BinarySymmetricSquareAction
