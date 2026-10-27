import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalRootCandidates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUniformRootMatrixArithmetic

/-! A primitive natural POSITIVE B matrix family with literal coordinates.
The toral matrices here are D_i, not the original terminal coroot 2D_last.
This is a target-side calculation, not a source-span assertion. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveMatrixCoordinates
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBOriginalRootCandidates
variable (R : Type*) [CommRing R] (r : ℕ)
abbrev PositiveIndex := Fin r ⊕ RootIndex r
local instance : DecidableEq (PositiveIndex r) := Classical.decEq _

def entry : PositiveIndex r → Index r × Index r
  | .inl i => (pos r i, pos r i)
  | .inr (.inl ij) => (pos r ij.val.1, pos r ij.val.2)
  | .inr (.inr (.inl i)) => (pos r i, middle r)
  | .inr (.inr (.inr ij)) => (pos r ij.val.1, neg r ij.val.2)

def matrix : PositiveIndex r → Mat R r
  | .inl i => Matrix.single (pos r i) (pos r i) 1 -
      Matrix.single (neg r i) (neg r i) 1
  | .inr (.inl ij) => CFSGOrthogonalBUniformRootMatrixArithmetic.difference R r ij.val.1 ij.val.2
  | .inr (.inr (.inl i)) => CFSGOrthogonalBUniformRootMatrixArithmetic.short R r i
  | .inr (.inr (.inr ij)) => CFSGOrthogonalBUniformRootMatrixArithmetic.sumRoot R r ij.val.1 ij.val.2

def coordinates : Mat R r →ₗ[R] (PositiveIndex r → R) where
  toFun M j := M (entry r j).1 (entry r j).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def decode : Index r × Index r → Option (PositiveIndex r)
  | (.inl (.inl i), .inl (.inl j)) =>
    if i = j then some (.inl i)
    else if hij : i.val < j.val then some (.inr (.inl ⟨(i, j), hij⟩)) else none
  | (.inl (.inl i), .inl (.inr j)) =>
    if hij : i.val < j.val then some (.inr (.inr (.inr ⟨(i, j), hij⟩))) else none
  | (.inl (.inl i), .inr _) => some (.inr (.inr (.inl i)))
  | _ => none

private def partner : PositiveIndex r → Index r × Index r
  | .inl i => (neg r i, neg r i)
  | .inr (.inl ij) => (neg r ij.val.2, neg r ij.val.1)
  | .inr (.inr (.inl i)) => (middle r, neg r i)
  | .inr (.inr (.inr ij)) => (pos r ij.val.2, neg r ij.val.1)

private def extraCoefficient : PositiveIndex r → R
  | .inr (.inr (.inl _)) => -2
  | _ => -1

private theorem pair_ne (ij : Pair r) : ij.val.1 ≠ ij.val.2 := by
  intro he
  have hv := congrArg Fin.val he
  have hh := ij.property
  omega

private theorem decode_entry (j : PositiveIndex r) : decode r (entry r j) = some j := by
  rcases j with i | (ij | (i | ij))
  · simp [entry, decode, pos]
  · simp [entry, decode, pos, pair_ne r ij, ij.property]
  · rfl
  · simp [entry, decode, pos, neg, ij.property]

private theorem decode_partner (j : PositiveIndex r) : decode r (partner r j) = none := by
  rcases j with i | (ij | (i | ij))
  · rfl
  · rfl
  · rfl
  · simp [partner, decode, pos, neg, not_lt_of_ge ij.property.le]

private theorem entry_injective : Function.Injective (entry r) := by
  intro j k he
  have hd := congrArg (decode r) he
  rw [decode_entry, decode_entry] at hd
  exact Option.some.inj hd

private theorem entry_ne_partner (j k : PositiveIndex r) : entry r k ≠ partner r j := by
  intro he
  have hd := congrArg (decode r) he
  rw [decode_entry, decode_partner] at hd
  cases hd

private theorem matrix_formula (j : PositiveIndex r) :
    matrix R r j = Matrix.single (entry r j).1 (entry r j).2 1 +
      extraCoefficient R r j • Matrix.single (partner r j).1 (partner r j).2 1 := by
  rcases j with i | (ij | (i | ij)) <;>
    simp [matrix, entry, partner, extraCoefficient,
      CFSGOrthogonalBUniformRootMatrixArithmetic.difference,
      CFSGOrthogonalBUniformRootMatrixArithmetic.short,
      CFSGOrthogonalBUniformRootMatrixArithmetic.sumRoot,
      sub_eq_add_neg, Matrix.smul_single]

theorem coordinates_matrix (j : PositiveIndex r) :
    coordinates R r (matrix R r j) = Pi.single j 1 := by
  funext k
  change matrix R r j (entry r k).1 (entry r k).2 = (Pi.single j 1 : PositiveIndex r → R) k
  rw [matrix_formula, Matrix.add_apply, Matrix.smul_apply]
  have hp : ¬ ((partner r j).1 = (entry r k).1 ∧ (partner r j).2 = (entry r k).2) := by
    intro h
    exact entry_ne_partner r j k (Prod.ext h.1 h.2).symm
  rw [Matrix.single_apply_of_ne _ _ _ _ _ hp, smul_zero, add_zero]
  by_cases h : j = k
  · subst k
    rw [Matrix.single_apply_same]
    simp only [Pi.single_apply, if_true]
  · have he : entry r j ≠ entry r k := fun he => h (entry_injective r he)
    have hp' : ¬ ((entry r j).1 = (entry r k).1 ∧ (entry r j).2 = (entry r k).2) :=
      fun h => he (Prod.ext h.1 h.2)
    rw [Matrix.single_apply_of_ne _ _ _ _ _ hp']
    simp only [Pi.single_apply, h, Ne.symm h, if_false]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveMatrixCoordinates
