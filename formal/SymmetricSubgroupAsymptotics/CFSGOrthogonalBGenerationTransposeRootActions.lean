import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationElements
import Mathlib.Algebra.CharP.Two

/-! Sparse transpose actions of the literal B root matrices. In
characteristic two the terminal short roots still retain their quadratic
coefficient; the middle-coordinate shear cancels it in the quadratic form. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationTransposeRootActions
open CFSGOrthogonalBSerreMatrices
variable (K : Type) [Field K] [CharP K 2]

omit [CharP K 2] in
private theorem single_action_apply {I : Type*} [Fintype I] [DecidableEq I]
    (a b j : I) (c : K) (v : I → K) :
    (Matrix.single a b c *ᵥ v) j = if j = a then c * v b else 0 := by
  rw [Matrix.single_mulVec]
  simp [Function.update_apply]

theorem positive_chain (r : ℕ) (i : Fin r) (hi : i.val + 1 < r)
    (t : K) (v : Index r → K) (j : Index r) :
    ((rootTransvection K r false i t : Mat K r)ᵀ *ᵥ v) j =
      v j + (if j = pos r ⟨i.val + 1, hi⟩ then t * v (pos r i) else 0) -
        (if j = neg r i then t * v (neg r ⟨i.val + 1, hi⟩) else 0) := by
  simp [rootTransvection_val, rootMatrix, rootSecond, positive, positiveSecond, hi,
    Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    single_action_apply, Matrix.neg_mulVec, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, mul_ite, ite_mul]
  all_goals try split_ifs
  all_goals ring

theorem negative_chain (r : ℕ) (i : Fin r) (hi : i.val + 1 < r)
    (t : K) (v : Index r → K) (j : Index r) :
    ((rootTransvection K r true i t : Mat K r)ᵀ *ᵥ v) j =
      v j + (if j = pos r i then t * v (pos r ⟨i.val + 1, hi⟩) else 0) -
        (if j = neg r ⟨i.val + 1, hi⟩ then t * v (neg r i) else 0) := by
  simp [rootTransvection_val, rootMatrix, rootSecond, negative, negativeSecond, hi,
    Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    single_action_apply, Matrix.neg_mulVec, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, mul_ite, ite_mul]
  all_goals try split_ifs
  all_goals ring

theorem positive_short (r : ℕ) (i : Fin r) (hi : ¬ i.val + 1 < r)
    (t : K) (v : Index r → K) (j : Index r) :
    ((rootTransvection K r false i t : Mat K r)ᵀ *ᵥ v) j =
      v j + (if j = middle r then t * v (pos r i) else 0) -
        (if j = neg r i then t ^ 2 * v (pos r i) else 0) := by
  simp [rootTransvection_val, rootMatrix, rootSecond, positive, positiveSecond, hi,
    Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    single_action_apply, Matrix.neg_mulVec, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, CharTwo.two_eq_zero, mul_ite, ite_mul]
  all_goals try split_ifs
  all_goals ring

theorem negative_short (r : ℕ) (i : Fin r) (hi : ¬ i.val + 1 < r)
    (t : K) (v : Index r → K) (j : Index r) :
    ((rootTransvection K r true i t : Mat K r)ᵀ *ᵥ v) j =
      v j - (if j = middle r then t * v (neg r i) else 0) -
        (if j = pos r i then t ^ 2 * v (neg r i) else 0) := by
  simp [rootTransvection_val, rootMatrix, rootSecond, negative, negativeSecond, hi,
    Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    single_action_apply, Matrix.neg_mulVec, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, CharTwo.two_eq_zero, mul_ite, ite_mul]
  all_goals try split_ifs
  all_goals ring

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationTransposeRootActions
