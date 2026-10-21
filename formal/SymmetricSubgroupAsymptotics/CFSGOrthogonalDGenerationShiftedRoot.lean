import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSignedRootConjugation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationInitialRootMatrices

/-! The actual conjugated short root W*A*W^-1 is e2-e1. It is retained
as an original D word, with its full parameter and both matrix entries. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationShiftedRoot
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDGenerationInitialElements CFSGOrthogonalDGenerationInitialRootMatrices
open CFSGOrthogonalDGenerationForkTorus CFSGOrthogonalDBinaryCyclePermutation
open CFSGOrthogonalDGenerationSignedRootConjugation CFSGOrthogonalDGenerationCoxeterMonomial
open CFSGOrthogonalDGenerationCoxeterSigns
variable (K : Type) [Field K]

def third (s : ℕ) : Fin (s + 4) := ⟨2, by omega⟩

theorem third_ne_second (s : ℕ) : third s ≠ second s := by
  intro h
  have hv := congrArg Fin.val h
  change 2 = 1 at hv
  omega

theorem third_ne_last (s : ℕ) : third s ≠ last (s + 2) := by
  intro h
  have hv := congrArg Fin.val h
  change 2 = s + 3 at hv
  omega

def shiftedShortRoot (s : ℕ) (a : K) : elementaryRootGroup K (s + 4) :=
  coxeterWeyl K (s + 3) * initialShortRoot K s a * (coxeterWeyl K (s + 3))⁻¹

@[simp] theorem shiftedShortRoot_zero (s : ℕ) : shiftedShortRoot K s 0 = 1 := by
  simp only [shiftedShortRoot, initialShortRoot_zero, mul_one, mul_inv_cancel]

theorem shiftedShortRoot_add (s : ℕ) (a b : K) :
    shiftedShortRoot K s (a + b) = shiftedShortRoot K s a * shiftedShortRoot K s b := by
  simp only [shiftedShortRoot, initialShortRoot_add, mul_assoc, inv_mul_cancel_left]

theorem shiftedShortRoot_coe (s : ℕ) (a : K) :
    ((shiftedShortRoot K s a).val : Mat K (s + 4)) =
      1 + Matrix.single (Sum.inl (third s)) (Sum.inl (second s)) a -
        Matrix.single (Sum.inr (second s)) (Sum.inr (third s)) a := by
  have h0 : coxeterColumnSign K (s + 2) (Sum.inl (0 : Fin (s + 4))) = 1 := by
    rw [coxeterColumnSign_profile]
    change (if (0 : Fin (s + 4)) = pen (s + 2) then (-1 : K) ^ (s + 3)
      else if 0 = last (s + 2) then -1 else 1) = 1
    simp [Ne.symm (pen_ne_zero s), Ne.symm (last_ne_zero s)]
  have h1 : coxeterColumnSign K (s + 2) (Sum.inl (second s)) = 1 := by
    rw [coxeterColumnSign_profile]
    change (if second s = pen (s + 2) then (-1 : K) ^ (s + 3)
      else if second s = last (s + 2) then -1 else 1) = 1
    simp [second_ne_pen, second_ne_last]
  have hm0 : cyclePerm (s + 2) (Sum.inl (0 : Fin (s + 4))) = Sum.inl (second s) :=
    cyclePerm_shift (s + 2) false 0 (by omega)
  have hm1 : cyclePerm (s + 2) (Sum.inl (second s)) = Sum.inl (third s) :=
    cyclePerm_shift (s + 2) false 1 (by omega)
  change ((coxeterWeyl K (s + 3)).val : Mat K (s + 4)) *
    ((initialShortRoot K s a).val : Mat K (s + 4)) *
      (↑((coxeterWeyl K (s + 3)).val⁻¹) : Mat K (s + 4)) = _
  rw [initialShortRoot_coe]
  change ((coxeterWeyl K (s + 3)).val : Mat K (s + 4)) *
    rootArray K (Sum.inl (second s)) (Sum.inl (0 : Fin (s + 4))) a *
      (↑((coxeterWeyl K (s + 3)).val⁻¹) : Mat K (s + 4)) = _
  rw [coxeter_conjugation K (s + 2), hm0, hm1, h0, h1]
  simp only [one_mul, div_one, rootArray, paired]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationShiftedRoot
