import SymmetricSubgroupAsymptotics.CFSGMatrixFlagNormalizer
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The actual flag-prefix submodule has its exact coordinate dimension.
This will measure the remaining final-pair swap without a census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPrefixDimension
open CFSGMatrixFlagNormalizer
variable (K : Type*) [Field K] {I : Type*}
variable {m : ℕ} (e : I ≃ Fin m)

def prefixParameters (k : ℕ) (hk : k ≤ m) :
    (Fin k → K) ≃ₗ[K] flagPrefix (K := K) e k where
  toFun x := ⟨fun i => if hi : (e i).val < k then x ⟨(e i).val, hi⟩ else 0, by
    intro i hi
    change (if h : (e i).val < k then x ⟨(e i).val, h⟩ else 0) = 0
    rw [dif_neg (not_lt_of_ge hi)]⟩
  invFun x j := x.val (e.symm ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)
  left_inv x := by
    funext j
    change (if hi : (e (e.symm ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)).val < k
      then x ⟨(e (e.symm ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)).val, hi⟩ else 0) = x j
    simp only [e.apply_symm_apply]
    rw [dif_pos j.isLt]
  right_inv x := by
    apply Subtype.ext
    funext i
    change (if hi : (e i).val < k then
      x.val (e.symm ⟨(e i).val, Nat.lt_of_lt_of_le hi hk⟩) else 0) = x.val i
    by_cases hi : (e i).val < k
    · rw [dif_pos hi]
      have he : (⟨(e i).val, Nat.lt_of_lt_of_le hi hk⟩ : Fin m) = e i := rfl
      rw [he, e.symm_apply_apply]
    · rw [dif_neg hi]
      exact (x.property i (Nat.le_of_not_gt hi)).symm
  map_add' x y := by
    apply Subtype.ext
    funext i
    change (if hi : (e i).val < k then (x + y) ⟨(e i).val, hi⟩ else 0) =
      (if hi : (e i).val < k then x ⟨(e i).val, hi⟩ else 0) +
        (if hi : (e i).val < k then y ⟨(e i).val, hi⟩ else 0)
    by_cases hi : (e i).val < k
    · simp only [dif_pos hi, Pi.add_apply]
    · simp only [dif_neg hi, add_zero]
  map_smul' c x := by
    apply Subtype.ext
    funext i
    change (if hi : (e i).val < k then (c • x) ⟨(e i).val, hi⟩ else 0) =
      c • (if hi : (e i).val < k then x ⟨(e i).val, hi⟩ else 0)
    by_cases hi : (e i).val < k
    · simp only [dif_pos hi, Pi.smul_apply]
    · simp only [dif_neg hi, smul_zero]

theorem flagPrefix_finrank (k : ℕ) (hk : k ≤ m) :
    Module.finrank K (flagPrefix (K := K) e k) = k := by
  simpa using (prefixParameters K e k hk).finrank_eq.symm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPrefixDimension
