import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationCoxeterSigns
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationMonomialAction

/-! Actual Coxeter transport of a parameterized D root, uniformly in
both coordinate signs. The same field coefficient occurs in its two
entries because the paired Coxeter weights have product one. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSignedRootConjugation
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDBinaryCyclePermutation CFSGOrthogonalDGenerationCoxeterMonomial
open CFSGOrthogonalDGenerationCoxeterSigns CFSGOrthogonalDGenerationMonomialAction
variable (K : Type) [Field K]

def rootArray {r : ℕ} (a b : Index r) (t : K) : Mat K r :=
  1 + Matrix.single a b t - Matrix.single (paired b) (paired a) t

theorem coxeter_conjugation (s : ℕ) (a b : Index (s + 2)) (t : K) :
    ((coxeterWeyl K (s + 1)).val : Mat K (s + 2)) * rootArray K a b t *
      (↑((coxeterWeyl K (s + 1)).val⁻¹) : Mat K (s + 2)) =
      rootArray K (cyclePerm s a) (cyclePerm s b)
        (coxeterColumnSign K s a * t / coxeterColumnSign K s b) := by
  have hp (x : Index (s + 2)) :
      (cyclePerm s).symm (paired (cyclePerm s x)) = paired x := by
    rw [← cyclePerm_paired s x, Equiv.symm_apply_apply]
  have h := conjugation_two_entry (coxeterWeyl K (s + 1)).val (cyclePerm s).symm
    (coxeterColumnSign K s ∘ (cyclePerm s).symm) (coxeter_monomial K s)
    a b (paired b) (paired a) t
    (by simpa only [Equiv.symm_symm, Function.comp_apply, Equiv.symm_apply_apply] using
      coxeterColumnSign_ne_zero K s b)
    (by simpa only [Equiv.symm_symm, Function.comp_apply, Equiv.symm_apply_apply] using
      coxeterColumnSign_ne_zero K s (paired a))
  simpa only [rootArray, Equiv.symm_symm, Function.comp_apply,
    Equiv.symm_apply_apply, cyclePerm_paired, hp, paired_ratio] using h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSignedRootConjugation
