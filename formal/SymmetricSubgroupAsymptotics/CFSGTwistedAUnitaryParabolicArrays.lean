import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperMiddleArrays

/-! Literal parabolic block equations. A form-isometry fixing the first
basis vector has the exact final covector, so it has the actual
upper/radical/middle block shape. These statements require no triangular
hypothesis on the middle block and no named-group recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays
variable {K J : Type*} [CommRing K] [Fintype J] [DecidableEq J]

theorem isometry_first_column_last_row (f : K →+* K) (eps : K)
    (H : Matrix J J K) (M : Matrix (Index J) (Index J) K)
    (hM : (M.map f).transpose * blockForm eps H * M = blockForm eps H)
    (hcol : ∀ i, M i (.inl ()) = if i = .inl () then 1 else 0) :
    ∀ j, M (.inr (.inr ())) j = if j = .inr (.inr ()) then 1 else 0 := by
  intro j
  have he := congrArg (fun A : Matrix (Index J) (Index J) K => A (.inl ()) j) hM
  dsimp only at he
  rcases j with u | (j | u)
  all_goals try cases u
  all_goals simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Fintype.sum_sum_type, hcol, blockForm] using he

theorem parabolic_block_shape (M : Matrix (Index J) (Index J) K)
    (hcol : ∀ i, M i (.inl ()) = if i = .inl () then 1 else 0)
    (hrow : ∀ j, M (.inr (.inr ())) j = if j = .inr (.inr ()) then 1 else 0) :
    M = upperMiddleArray (fun j => M (.inl ()) (.inr (.inl j)))
      (fun i j => M (.inr (.inl i)) (.inr (.inl j)))
      (fun i => M (.inr (.inl i)) (.inr (.inr ()))) (M (.inl ()) (.inr (.inr ()))) := by
  ext (u | (i | u)) (v | (j | v))
  all_goals try cases u
  all_goals try cases v
  all_goals try rfl
  all_goals simp only [upperMiddleArray]
  all_goals first | simpa using hcol _ | simpa using hrow _

theorem upperMiddleArray_det (w v : J → K) (b : K) (A : Matrix J J K) :
    (upperMiddleArray w A v b).det = A.det := by
  have he : upperMiddleArray w A v b =
      Matrix.fromBlocks (1 : Matrix Unit Unit K)
        (fun _ j => match j with | .inl k => w k | .inr _ => b) 0
        (Matrix.fromBlocks A (fun i _ => v i) 0 (1 : Matrix Unit Unit K)) := by
    ext (u | (i | u)) (z | (j | z))
    all_goals simp [upperMiddleArray, Matrix.fromBlocks, Matrix.one_apply]
  rw [he, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁]
  simp

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays
