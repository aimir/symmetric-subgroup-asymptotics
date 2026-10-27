import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveMatrixCoordinates

/-! Primitive full natural B coordinates. The negative short-root entry
has sign minus one; this sign is retained. This target-side family uses
diagonal D_i rather than asserting the original coroots are primitive. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBFullMatrixCoordinates
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBOriginalRootCandidates
variable (R : Type*) [CommRing R] (r : ℕ)
local instance : DecidableEq (BasisIndex r) := Classical.decEq _

def entry : BasisIndex r → Index r × Index r
  | .inl i => (pos r i, pos r i)
  | .inr (false, .inl ij) => (pos r ij.val.1, pos r ij.val.2)
  | .inr (true, .inl ij) => (pos r ij.val.2, pos r ij.val.1)
  | .inr (false, .inr (.inl i)) => (pos r i, middle r)
  | .inr (true, .inr (.inl i)) => (neg r i, middle r)
  | .inr (false, .inr (.inr ij)) => (pos r ij.val.1, neg r ij.val.2)
  | .inr (true, .inr (.inr ij)) => (neg r ij.val.2, pos r ij.val.1)

def sign : BasisIndex r → R
  | .inr (true, .inr (.inl _)) => -1
  | _ => 1

def matrix : BasisIndex r → Mat R r
  | .inl i => Matrix.single (pos r i) (pos r i) 1 - Matrix.single (neg r i) (neg r i) 1
  | .inr (false, .inl ij) => CFSGOrthogonalBUniformRootMatrixArithmetic.difference R r ij.val.1 ij.val.2
  | .inr (true, .inl ij) => (CFSGOrthogonalBUniformRootMatrixArithmetic.difference R r ij.val.1 ij.val.2).transpose
  | .inr (false, .inr (.inl i)) => CFSGOrthogonalBUniformRootMatrixArithmetic.short R r i
  | .inr (true, .inr (.inl i)) => Matrix.single (middle r) (pos r i) 2 - Matrix.single (neg r i) (middle r) 1
  | .inr (false, .inr (.inr ij)) => CFSGOrthogonalBUniformRootMatrixArithmetic.sumRoot R r ij.val.1 ij.val.2
  | .inr (true, .inr (.inr ij)) => (CFSGOrthogonalBUniformRootMatrixArithmetic.sumRoot R r ij.val.1 ij.val.2).transpose

def coordinates : Mat R r →ₗ[R] (BasisIndex r → R) where
  toFun M j := sign R r j * M (entry r j).1 (entry r j).2
  map_add' _ _ := by funext j; simp only [Matrix.add_apply, Pi.add_apply, mul_add]
  map_smul' _ _ := by funext j; simp only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private def decode : Index r × Index r → Option (BasisIndex r)
  | (.inl (.inl i), .inl (.inl j)) =>
    if h : i = j then some (.inl i)
    else if hij : i.val < j.val then some (.inr (false, .inl ⟨(i, j), hij⟩))
    else some (.inr (true, .inl ⟨(j, i), by
      change j.val < i.val
      have hn : i.val ≠ j.val := fun he => h (Fin.ext he)
      omega⟩))
  | (.inl (.inl i), .inl (.inr j)) =>
    if hij : i.val < j.val then some (.inr (false, .inr (.inr ⟨(i, j), hij⟩))) else none
  | (.inl (.inr i), .inl (.inl j)) =>
    if hji : j.val < i.val then some (.inr (true, .inr (.inr ⟨(j, i), hji⟩))) else none
  | (.inl (.inl i), .inr _) => some (.inr (false, .inr (.inl i)))
  | (.inl (.inr i), .inr _) => some (.inr (true, .inr (.inl i)))
  | _ => none

private def partner : BasisIndex r → Index r × Index r
  | .inl i => (neg r i, neg r i)
  | .inr (false, .inl ij) => (neg r ij.val.2, neg r ij.val.1)
  | .inr (true, .inl ij) => (neg r ij.val.1, neg r ij.val.2)
  | .inr (false, .inr (.inl i)) => (middle r, neg r i)
  | .inr (true, .inr (.inl i)) => (middle r, pos r i)
  | .inr (false, .inr (.inr ij)) => (pos r ij.val.2, neg r ij.val.1)
  | .inr (true, .inr (.inr ij)) => (neg r ij.val.1, pos r ij.val.2)

private def extraCoefficient : BasisIndex r → R
  | .inr (false, .inr (.inl _)) => -2
  | .inr (true, .inr (.inl _)) => 2
  | _ => -1

private theorem pair_ne (ij : Pair r) : ij.val.1 ≠ ij.val.2 := by
  intro h
  have hv := congrArg Fin.val h
  have hp := ij.property
  omega

private theorem decode_entry (j : BasisIndex r) : decode r (entry r j) = some j := by
  rcases j with i | ⟨neg, j⟩
  · simp [entry, decode, pos]
  · cases neg <;> rcases j with ij | (i | ij)
    · simp [entry, decode, pos, pair_ne r ij, ij.property]
    · rfl
    · simp [entry, decode, pos, neg, ij.property]
    · simp [entry, decode, pos, Ne.symm (pair_ne r ij), not_lt_of_ge ij.property.le]
    · rfl
    · simp [entry, decode, pos, neg, ij.property]

private theorem decode_partner (j : BasisIndex r) : decode r (partner r j) = none := by
  rcases j with i | ⟨neg, j⟩
  · rfl
  · cases neg <;> rcases j with ij | (i | ij)
    · rfl
    · rfl
    · simp [partner, decode, pos, neg, not_lt_of_ge ij.property.le]
    · rfl
    · rfl
    · simp [partner, decode, pos, neg, not_lt_of_ge ij.property.le]

private theorem entry_injective : Function.Injective (entry r) := by
  intro j k h
  have hd := congrArg (decode r) h
  rw [decode_entry, decode_entry] at hd
  exact Option.some.inj hd

private theorem entry_ne_partner (j k : BasisIndex r) : entry r k ≠ partner r j := by
  intro h
  have hd := congrArg (decode r) h
  rw [decode_entry, decode_partner] at hd
  cases hd

private theorem sign_sq (j : BasisIndex r) : sign R r j * sign R r j = 1 := by
  rcases j with i | ⟨neg, j⟩
  · simp [sign]
  · cases neg <;> rcases j with ij | (i | ij) <;> simp [sign]

private theorem matrix_formula (j : BasisIndex r) :
    matrix R r j = sign R r j • Matrix.single (entry r j).1 (entry r j).2 1 +
      extraCoefficient R r j • Matrix.single (partner r j).1 (partner r j).2 1 := by
  rcases j with i | ⟨neg, j⟩
  · simp [matrix, entry, partner, sign, extraCoefficient, sub_eq_add_neg]
  · cases neg <;> rcases j with ij | (i | ij) <;>
      simp [matrix, entry, partner, sign, extraCoefficient,
        CFSGOrthogonalBUniformRootMatrixArithmetic.difference,
        CFSGOrthogonalBUniformRootMatrixArithmetic.short,
        CFSGOrthogonalBUniformRootMatrixArithmetic.sumRoot,
        Matrix.transpose_sub, Matrix.transpose_single, sub_eq_add_neg,
        Matrix.smul_single, add_comm]

theorem coordinates_matrix (j : BasisIndex r) :
    coordinates R r (matrix R r j) = Pi.single j 1 := by
  funext k
  change sign R r k * matrix R r j (entry r k).1 (entry r k).2 =
    (Pi.single j 1 : BasisIndex r → R) k
  rw [matrix_formula, Matrix.add_apply]
  simp only [Matrix.smul_apply]
  have hp : ¬ ((partner r j).1 = (entry r k).1 ∧ (partner r j).2 = (entry r k).2) := by
    intro h
    exact entry_ne_partner r j k (Prod.ext h.1 h.2).symm
  rw [Matrix.single_apply_of_ne _ _ _ _ _ hp, smul_zero, add_zero]
  by_cases h : j = k
  · subst k
    rw [Matrix.single_apply_same]
    simpa only [smul_eq_mul, mul_one, Pi.single_apply, if_true] using sign_sq R r j
  · have he : entry r j ≠ entry r k := fun he => h (entry_injective r he)
    have hp' : ¬ ((entry r j).1 = (entry r k).1 ∧ (entry r j).2 = (entry r k).2) :=
      fun he' => he (Prod.ext he'.1 he'.2)
    rw [Matrix.single_apply_of_ne _ _ _ _ _ hp']
    simp only [smul_zero, mul_zero, Pi.single_apply, h, Ne.symm h, if_false]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBFullMatrixCoordinates
