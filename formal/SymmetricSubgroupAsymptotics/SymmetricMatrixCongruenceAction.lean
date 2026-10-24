import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Lean.Elab.Tactic.Omega

/-! Actual symmetric n by n matrices and their literal GL_n congruence
action. An upper-triangle projection is linear in every characteristic;
it never divides by two. It will be used to reconstruct genuine
prime-field functionals without assuming coefficient-field linearity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.SymmetricMatrixCongruenceAction

variable {K : Type*} [Field K] (n : ℕ)
abbrev GeneralLinear := (Matrix (Fin n) (Fin n) K)ˣ

def symmetricSubmodule : Submodule K (Matrix (Fin n) (Fin n) K) where
  carrier := {S | S.IsSymm}
  zero_mem' := Matrix.isSymm_zero
  add_mem' := fun hS hT => hS.add hT
  smul_mem' := fun r _ hS => hS.smul r

abbrev Space := symmetricSubmodule (K := K) n

def congruenceLinearMap (A : GeneralLinear (K := K) n) :
    Space (K := K) n →ₗ[K] Space (K := K) n where
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

@[simp] theorem congruenceLinearMap_one (S : Space (K := K) n) :
    congruenceLinearMap n 1 S = S := by
  apply Subtype.ext
  change (1 : Matrix (Fin n) (Fin n) K) * S.val *
    (1 : Matrix (Fin n) (Fin n) K).transpose = S.val
  rw [Matrix.transpose_one, one_mul, mul_one]

theorem congruenceLinearMap_mul (A B : GeneralLinear (K := K) n) (S : Space (K := K) n) :
    congruenceLinearMap n (A * B) S = congruenceLinearMap n A (congruenceLinearMap n B S) := by
  apply Subtype.ext
  change (A.val * B.val) * S.val * (A.val * B.val).transpose =
    A.val * (B.val * S.val * B.val.transpose) * A.val.transpose
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

def congruence : GeneralLinear (K := K) n →* Space (K := K) n ≃ₗ[K] Space (K := K) n where
  toFun A := {
    congruenceLinearMap n A with
    invFun := congruenceLinearMap n A⁻¹
    left_inv := by
      intro S
      change congruenceLinearMap n A⁻¹ (congruenceLinearMap n A S) = S
      rw [← congruenceLinearMap_mul, inv_mul_cancel, congruenceLinearMap_one]
    right_inv := by
      intro S
      change congruenceLinearMap n A (congruenceLinearMap n A⁻¹ S) = S
      rw [← congruenceLinearMap_mul, mul_inv_cancel, congruenceLinearMap_one] }
  map_one' := by apply LinearEquiv.ext; intro S; exact congruenceLinearMap_one n S
  map_mul' A B := by apply LinearEquiv.ext; intro S; exact congruenceLinearMap_mul n A B S

def rankOne (v : Fin n → K) : Space (K := K) n :=
  ⟨Matrix.vecMulVec v v, Matrix.transpose_vecMulVec v v⟩

theorem rankOne_congruence (A : GeneralLinear (K := K) n) (v : Fin n → K) :
    congruenceLinearMap n A (rankOne n v) = rankOne n (A.val *ᵥ v) := by
  apply Subtype.ext
  change A.val * Matrix.vecMulVec v v * A.val.transpose =
    Matrix.vecMulVec (A.val *ᵥ v) (A.val *ᵥ v)
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

/-- Copy upper entries into the lower triangle, with no factor two. -/
def upperProjection : Matrix (Fin n) (Fin n) K →ₗ[K] Space (K := K) n where
  toFun M := ⟨fun i j => if i ≤ j then M i j else M j i, by
    apply Matrix.IsSymm.ext
    intro i j
    by_cases he : i = j
    · subst j; rfl
    · by_cases hi : i ≤ j
      · have hj : ¬j ≤ i := fun h => he (le_antisymm hi h)
        simp only [hi, hj, if_true, if_false]
      · have hj : j ≤ i := le_of_not_ge hi
        simp only [hi, hj, if_true, if_false]⟩
  map_add' M N := by
    apply Subtype.ext
    ext i j
    change (if i ≤ j then M i j + N i j else M j i + N j i) =
      (if i ≤ j then M i j else M j i) + (if i ≤ j then N i j else N j i)
    by_cases h : i ≤ j <;> simp only [h, if_true, if_false]
  map_smul' a M := by
    apply Subtype.ext
    ext i j
    change (if i ≤ j then a * M i j else a * M j i) =
      a * (if i ≤ j then M i j else M j i)
    by_cases h : i ≤ j <;> simp only [h, if_true, if_false]

theorem upperProjection_symmetric (S : Space (K := K) n) : upperProjection n S.val = S := by
  apply Subtype.ext
  ext i j
  change (if i ≤ j then S.val i j else S.val j i) = S.val i j
  by_cases hi : i ≤ j
  · rw [if_pos hi]
  · rw [if_neg hi]
    exact S.property.apply i j

end SymmetricSubgroupAsymptotics.SymmetricMatrixCongruenceAction
