import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalSignedForm
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperIsometry

/-! Exact natural-coordinate binding of the three-block radical form.
The ORIGINAL signedReversalUnit in rank s+2 splits as a hyperbolic pair
and minus the ORIGINAL signed reversal in rank s. No chosen Hermitian
form equivalence or unitary model hypothesis is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays

def splitIndex (s : ℕ) : Index (Fin (s + 1)) → Fin (s + 3)
  | .inl _ => 0
  | .inr (.inl i) => ⟨i.val + 1, by have hi := i.isLt; omega⟩
  | .inr (.inr _) => Fin.last (s + 2)

def splitEquiv (s : ℕ) : Index (Fin (s + 1)) ≃ Fin (s + 3) where
  toFun := splitIndex s
  invFun i := if h0 : i.val = 0 then .inl ()
    else if hl : i.val = s + 2 then .inr (.inr ())
    else .inr (.inl ⟨i.val - 1, by have hi := i.isLt; omega⟩)
  left_inv := by
    rintro (u | (i | u))
    · cases u
      simp [splitIndex]
    · have h0 : i.val + 1 ≠ 0 := by omega
      have hl : i.val + 1 ≠ s + 2 := by have hi := i.isLt; omega
      simp only [splitIndex, dif_neg h0, dif_neg hl]
      apply congrArg Sum.inr
      apply congrArg Sum.inl
      apply Fin.ext
      dsimp only
      omega
    · cases u
      have h0 : s + 2 ≠ 0 := by omega
      simp [splitIndex, h0]
  right_inv := by
    intro i
    by_cases h0 : i.val = 0
    · simp only [dif_pos h0, splitIndex]
      exact Fin.ext h0.symm
    · simp only [dif_neg h0]
      by_cases hl : i.val = s + 2
      · simp only [dif_pos hl, splitIndex]
        exact Fin.ext hl.symm
      · simp only [dif_neg hl, splitIndex]
        apply Fin.ext
        dsimp only
        omega

theorem splitIndex_inj (s : ℕ) (i j : Index (Fin (s + 1))) :
    splitIndex s i = splitIndex s j ↔ i = j :=
  (splitEquiv s).injective.eq_iff

theorem split_head_rev (s : ℕ) :
    (splitIndex s (.inl ())).rev = splitIndex s (.inr (.inr ())) := by
  apply Fin.ext
  simp only [splitIndex, Fin.rev, Fin.val_zero, Fin.val_last]
  omega

theorem split_last_rev (s : ℕ) :
    (splitIndex s (.inr (.inr ()))).rev = splitIndex s (.inl ()) := by
  apply Fin.ext
  simp only [splitIndex, Fin.rev, Fin.val_zero, Fin.val_last]
  omega

theorem split_middle_rev (s : ℕ) (i : Fin (s + 1)) :
    (splitIndex s (.inr (.inl i))).rev = splitIndex s (.inr (.inl i.rev)) := by
  apply Fin.ext
  simp only [splitIndex, Fin.rev]
  have hi := i.isLt
  omega

theorem signWeight_split_head (R : Type*) [CommRing R] (s : ℕ) :
    signWeight R (s + 2) (splitIndex s (.inl ())) = 1 := by
  simp only [signWeight, splitIndex, Fin.val_zero, pow_zero]

theorem signWeight_split_last (R : Type*) [CommRing R] (s : ℕ) :
    signWeight R (s + 2) (splitIndex s (.inr (.inr ()))) = (-1 : R) ^ s := by
  change (-1 : R) ^ (s + 2) = (-1 : R) ^ s
  rw [pow_add]
  simp

theorem signWeight_split_middle (R : Type*) [CommRing R] (s : ℕ) (i : Fin (s + 1)) :
    signWeight R (s + 2) (splitIndex s (.inr (.inl i))) = -signWeight R s i := by
  change (-1 : R) ^ (i.val + 1) = -((-1 : R) ^ i.val)
  rw [pow_succ, mul_neg_one]

theorem signedForm_split (R : Type*) [CommRing R] (s : ℕ) :
    (signedReversalUnit R (s + 2) : Mat R (s + 2)).submatrix (splitIndex s) (splitIndex s) =
      blockForm ((-1 : R) ^ s) (-(signedReversalUnit R s : Mat R s)) := by
  ext (u | (i | u)) (v | (j | v))
  all_goals try cases u
  all_goals try cases v
  all_goals simp [Matrix.submatrix_apply, signedReversalUnit_apply, blockForm,
    split_head_rev, split_middle_rev, split_last_rev, splitIndex_inj,
    signWeight_split_head, signWeight_split_last, signWeight_split_middle, apply_ite]
  all_goals split_ifs <;> simp_all

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
