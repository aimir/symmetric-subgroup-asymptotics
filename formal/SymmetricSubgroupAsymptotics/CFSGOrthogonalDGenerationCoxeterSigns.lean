import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationCoxeterMonomial

/-! The paired coordinate weights of the literal D Coxeter word.
Both signs are retained, and their square-one identity supplies the
equal coefficient ratios required by the two entries of a D root. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationCoxeterSigns
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryCyclePermutation
open CFSGOrthogonalDGenerationForkAction CFSGOrthogonalDGenerationCoxeterMonomial
variable (K : Type) [Field K]

theorem coxeterColumnSign_profile (s : ℕ) (a : Index (s + 2)) :
    coxeterColumnSign K s a = match a with
      | Sum.inl i => if i = (Fin.last s).castSucc then (-1) ^ (s + 1)
        else if i = Fin.last (s + 1) then -1 else 1
      | Sum.inr i => if i = (Fin.last s).castSucc then (-1) ^ (s + 1)
        else if i = Fin.last (s + 1) then -1 else 1 := by
  cases a with
  | inl i =>
    by_cases hp : i = (Fin.last s).castSucc <;>
      by_cases hq : i = Fin.last (s + 1) <;>
      simp_all [coxeterColumnSign, forkColumnSign, prefixColumnSign, forkPerm,
        CFSGOrthogonalDGenerationForkTorus.last, CFSGOrthogonalDGenerationForkTorus.pen,
        Equiv.swap_apply_def, Fin.ext_iff]
  | inr i =>
    by_cases hp : i = (Fin.last s).castSucc <;>
      by_cases hq : i = Fin.last (s + 1) <;>
      simp_all [coxeterColumnSign, forkColumnSign, prefixColumnSign, forkPerm,
        CFSGOrthogonalDGenerationForkTorus.last, CFSGOrthogonalDGenerationForkTorus.pen,
        Equiv.swap_apply_def, Fin.ext_iff]

theorem coxeterColumnSign_paired (s : ℕ) (a : Index (s + 2)) :
    coxeterColumnSign K s (paired a) = coxeterColumnSign K s a := by
  cases a <;> simp only [paired, coxeterColumnSign_profile]

theorem coxeterColumnSign_square (s : ℕ) (a : Index (s + 2)) :
    coxeterColumnSign K s a * coxeterColumnSign K s a = 1 := by
  cases a <;> simp only [coxeterColumnSign_profile] <;> split_ifs <;> simp [← mul_pow]

theorem paired_ratio (s : ℕ) (a b : Index (s + 2)) (t : K) :
    coxeterColumnSign K s (paired b) * t / coxeterColumnSign K s (paired a) =
      coxeterColumnSign K s a * t / coxeterColumnSign K s b := by
  rw [coxeterColumnSign_paired, coxeterColumnSign_paired]
  apply (div_eq_div_iff (coxeterColumnSign_ne_zero K s a)
    (coxeterColumnSign_ne_zero K s b)).mpr
  calc
    coxeterColumnSign K s b * t * coxeterColumnSign K s b =
        (coxeterColumnSign K s b * coxeterColumnSign K s b) * t := by ring
    _ = t := by rw [coxeterColumnSign_square, one_mul]
    _ = (coxeterColumnSign K s a * coxeterColumnSign K s a) * t := by
      rw [coxeterColumnSign_square, one_mul]
    _ = coxeterColumnSign K s a * t * coxeterColumnSign K s a := by ring

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationCoxeterSigns
