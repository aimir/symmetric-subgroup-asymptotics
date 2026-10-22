import SymmetricSubgroupAsymptotics.CFSGGTwoShortWeylMatrices
import SymmetricSubgroupAsymptotics.CFSGMonomialProductCoordinates
import SymmetricSubgroupAsymptotics.CFSGMatrixPairRotationMonomial

/-! Both literal G2 simple Weyl words have exact signed-monomial
coordinates. These are actual matrix-unit words, with all row weights
retained, for transporting root parameters to all twelve directions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoWeylMonomial
open CFSGGTwoSerreMatrices CFSGGTwoShortWeylMatrices CFSGTypeAMonomialMatrices

def shortPermutation : Equiv.Perm Index :=
  Equiv.swap (pos 0) (pos 1) * Equiv.swap (neg 0) (neg 1) *
    Equiv.swap (pos 2) (neg 2) * Equiv.swap (pos 3) (neg 3)

def longPermutation : Equiv.Perm Index :=
  Equiv.swap (pos 1) (pos 2) * Equiv.swap (neg 1) (neg 2)

def shortWeight (K : Type*) [Field K] (x : Index) : K :=
  if x = pos 0 ∨ x = neg 0 then 1 else -1

def longWeight (K : Type*) [Field K] (x : Index) : K :=
  if x = pos 1 ∨ x = neg 1 then -1 else 1

theorem shortWeight_ne_zero (K : Type*) [Field K] (x : Index) : shortWeight K x ≠ 0 := by
  unfold shortWeight
  split_ifs <;> simp

theorem longWeight_ne_zero (K : Type*) [Field K] (x : Index) : longWeight K x ≠ 0 := by
  unfold longWeight
  split_ifs <;> simp

theorem shortWeyl_monomial (K : Type*) [Field K] :
    (shortWeyl K : Mat K) = monomial shortPermutation (shortWeight K) := by
  rw [shortWeyl_val]
  ext x y
  rcases x with i | i <;> rcases y with j | j <;> fin_cases i <;> fin_cases j <;>
    norm_num [shortSignedMatrix, monomial_apply, shortPermutation, shortWeight,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def, pos, neg,
      Matrix.single_apply, Sum.inl_ne_inr, Sum.inr_ne_inl, Fin.ext_iff]

theorem longWeyl_monomial (K : Type) [Field K] :
    (longWeyl K : Mat K) = monomial longPermutation (longWeight K) := by
  have hw : (longWeyl K : Mat K) =
      CFSGMatrixPairRotation.rotation K (pos 1) (pos 2) *
        CFSGMatrixPairRotation.rotation K (neg 1) (neg 2) := by
    rw [longWeyl_val]
    change CFSGOrthogonalDSerreMatrices.chainWeylMatrix K 3 (1 : Fin 3) = _
    exact CFSGOrthogonalDSerreMatrices.chainWeylMatrix_rotation K 3 1
  rw [hw, CFSGMatrixPairRotation.rotation_monomial K _ _ (by decide),
    CFSGMatrixPairRotation.rotation_monomial K _ _ (by decide),
    CFSGMonomialProductCoordinates.monomial_mul]
  ext x y
  rcases x with i | i <;> rcases y with j | j <;> fin_cases i <;> fin_cases j <;>
    norm_num [monomial_apply, longPermutation, longWeight, Equiv.Perm.mul_apply,
      Equiv.swap_apply_def, pos, neg, Sum.inl_ne_inr, Sum.inr_ne_inl, Fin.ext_iff]

end SymmetricSubgroupAsymptotics.CFSGGTwoWeylMonomial
