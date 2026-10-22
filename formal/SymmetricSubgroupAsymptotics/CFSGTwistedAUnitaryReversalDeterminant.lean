import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalForm
import Mathlib.Tactic.FinCases

/-! The SAME signed reversal used in the defining diagram involution
has determinant one, in every natural dimension. The proof uses its
literal outer hyperbolic block and the smaller signed reversal, rather
than an assumed special-unitary or Weyl-group identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays

def endsEquiv (J : Type*) : Index J ≃ Fin 2 ⊕ J where
  toFun
    | .inl _ => .inl 0
    | .inr (.inl j) => .inr j
    | .inr (.inr _) => .inl 1
  invFun
    | .inl i => if i = 0 then .inl () else .inr (.inr ())
    | .inr j => .inr (.inl j)
  left_inv := by
    rintro (u | (j | u))
    all_goals try cases u
    all_goals simp
  right_inv := by
    rintro (i | j)
    · fin_cases i <;> simp
    · rfl

theorem blockForm_reindex_ends {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
    (eps : R) (H : Matrix J J R) :
    Matrix.reindex (endsEquiv J) (endsEquiv J) (blockForm eps H) =
      Matrix.fromBlocks !![0, 1; eps, 0] 0 0 H := by
  ext i j
  obtain ⟨x, rfl⟩ := (endsEquiv J).surjective i
  obtain ⟨y, rfl⟩ := (endsEquiv J).surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases x with u | (i | u) <;> rcases y with v | (j | v)
  all_goals try cases u
  all_goals try cases v
  all_goals simp [endsEquiv, blockForm, Matrix.fromBlocks]

theorem blockForm_det {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
    (eps : R) (H : Matrix J J R) : (blockForm eps H).det = -eps * H.det := by
  calc
    _ = (Matrix.reindex (endsEquiv J) (endsEquiv J) (blockForm eps H)).det := by
      rw [Matrix.det_reindex_self]
    _ = -eps * H.det := by
      rw [blockForm_reindex_ends, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fin_two_of]
      simp

theorem signedReversalUnit_det_step (R : Type*) [CommRing R] (s : ℕ) :
    (signedReversalUnit R (s + 2) : Mat R (s + 2)).det =
      (signedReversalUnit R s : Mat R s).det := by
  rw [← blockForm_reindex R s, Matrix.det_reindex_self, blockForm_det, Matrix.det_neg]
  simp only [Fintype.card_fin, pow_succ]
  have hp : ((-1 : R) ^ s) * ((-1 : R) ^ s) = 1 := by
    rw [← mul_pow]
    simp
  calc
    _ = (((-1 : R) ^ s) * ((-1 : R) ^ s)) * (signedReversalUnit R s : Mat R s).det := by ring
    _ = _ := by rw [hp, one_mul]

theorem signedReversalUnit_det (R : Type*) [CommRing R] (r : ℕ) :
    (signedReversalUnit R r : Mat R r).det = 1 := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero =>
      have hm : (signedReversalUnit R 0 : Mat R 0) = 1 := by
        ext i j
        rw [Fin.eq_zero i, Fin.eq_zero j]
        simp [signedReversalUnit_apply, signWeight]
      rw [hm, Matrix.det_one]
    | succ r =>
      cases r with
      | zero =>
        rw [Matrix.det_fin_two]
        norm_num [signedReversalUnit_apply, signWeight, Fin.rev, Fin.ext_iff]
      | succ s =>
        rw [signedReversalUnit_det_step]
        exact ih s (by omega)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
