import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperIsometry

/-! Necessary signed-form equations on the actual radical entries.
These are extracted from literal matrix equality; no converse unitary
recognition or fixed-subgroup hypothesis is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays
variable {K J : Type*} [Field K] [Fintype J] [DecidableEq J]

theorem upperArray_isometry_left_entry (f : K →+* K) (eps : K)
    (H : Matrix J J K) (w v : J → K) (b : K)
    (h : ((upperArray w v b).map f).transpose * blockForm eps H * upperArray w v b = blockForm eps H)
    (i : J) : f (w i) + (H *ᵥ v) i = 0 := by
  rw [mul_assoc, blockForm_mul_upper] at h
  have he := congrArg (fun M : Matrix (Index J) (Index J) K =>
    M (.inr (.inl i)) (.inr (.inr ()))) h
  dsimp only at he
  simpa [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Fintype.sum_sum_type, blockForm, formTimesUpper, upperArray, apply_ite, ite_mul, mul_ite] using he

theorem upperArray_isometry_central_entry (f : K →+* K) (eps : K)
    (H : Matrix J J K) (w v : J → K) (b : K)
    (h : ((upperArray w v b).map f).transpose * blockForm eps H * upperArray w v b = blockForm eps H) :
    f b + dotProduct (f ∘ v) (H *ᵥ v) + eps * b = 0 := by
  rw [mul_assoc, blockForm_mul_upper] at h
  have he := congrArg (fun M : Matrix (Index J) (Index J) K =>
    M (.inr (.inr ())) (.inr (.inr ()))) h
  dsimp only at he
  simpa [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Fintype.sum_sum_type, blockForm, formTimesUpper, upperArray, dotProduct,
    Function.comp_def, add_assoc] using he

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays
