import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationForkAction
import SymmetricSubgroupAsymptotics.CFSGTypeAMonomialMatrices

/-! The original D Coxeter word as a signed monomial matrix over any
field. Its coordinate permutation is the already defined D cycle, but
its actual signs are retained in every conjugation parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationCoxeterMonomial
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDBinaryCyclePermutation CFSGOrthogonalDGenerationForkAction
open CFSGTypeAMonomialMatrices
variable (K : Type) [Field K]

def prefixColumnSign (r : ℕ) : Index (r + 1) → K
  | Sum.inl i => if i = Fin.last r then (-1) ^ r else 1
  | Sum.inr i => if i = Fin.last r then (-1) ^ r else 1

theorem prefixColumnSign_ne_zero (r : ℕ) (a : Index (r + 1)) :
    prefixColumnSign K r a ≠ 0 := by
  cases a <;> simp only [prefixColumnSign] <;> split_ifs
  all_goals first | exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero) | exact one_ne_zero

theorem chainPrefix_basis (r : ℕ) (a : Index (r + 1)) :
    ((chainPrefix K r).val : Mat K (r + 1)) *ᵥ Pi.single a 1 =
      prefixColumnSign K r a •
        Pi.single (Equiv.sumCongr (finRotate (r + 1)) (finRotate (r + 1)) a) 1 := by
  have hside (side : Bool) (i : Fin (r + 1)) :
      ((chainPrefix K r).val : Mat K (r + 1)) *ᵥ
          Pi.single (if side then Sum.inr i else Sum.inl i) 1 =
        (if i = Fin.last r then (-1 : K) ^ r else 1) •
          Pi.single (if side then Sum.inr (finRotate (r + 1) i)
            else Sum.inl (finRotate (r + 1) i)) 1 := by
    have hh := CFSGSymplecticSerreMatrices.chainWeylPrefix_basis K r r le_rfl side i.val
      (Nat.le_of_lt_succ i.isLt)
    by_cases hi : i.val < r
    · have hne : i ≠ Fin.last r := by intro h; have hv := congrArg Fin.val h; simp at hv; omega
      let j : Fin (r + 1) := ⟨i.val + 1, Nat.succ_lt_succ hi⟩
      simp only [hi, if_true] at hh
      rw [CFSGSymplecticSerreMatrices.naturalCoordinateBasis_val K r side i,
        CFSGSymplecticSerreMatrices.naturalCoordinateBasis_val K r side j] at hh
      rw [finRotate_of_lt hi, if_neg hne, one_smul]
      exact hh
    · have he : i = Fin.last r := by
        apply Fin.ext
        have hb := i.isLt
        change i.val = r
        omega
      subst i
      simp only [Fin.val_last, lt_self_iff_false, if_false, if_true] at hh
      have hlast := CFSGSymplecticSerreMatrices.naturalCoordinateBasis_val K r side (Fin.last r)
      have hzero := CFSGSymplecticSerreMatrices.naturalCoordinateBasis_val K r side (0 : Fin (r + 1))
      change CFSGSymplecticSerreMatrices.naturalCoordinateBasis K r side r = _ at hlast
      change CFSGSymplecticSerreMatrices.naturalCoordinateBasis K r side 0 = _ at hzero
      rw [hlast, hzero] at hh
      rw [finRotate_last, if_pos rfl]
      exact hh
  cases a with
  | inl i => exact hside false i
  | inr i => exact hside true i

def coxeterColumnSign (s : ℕ) (a : Index (s + 2)) : K :=
  forkColumnSign K s a * prefixColumnSign K (s + 1) (forkPerm s a)

theorem coxeterColumnSign_ne_zero (s : ℕ) (a : Index (s + 2)) :
    coxeterColumnSign K s a ≠ 0 :=
  mul_ne_zero (forkColumnSign_ne_zero K s a)
    (prefixColumnSign_ne_zero K (s + 1) (forkPerm s a))

theorem coxeter_basis (s : ℕ) (a : Index (s + 2)) :
    ((coxeterWeyl K (s + 1)).val : Mat K (s + 2)) *ᵥ Pi.single a 1 =
      coxeterColumnSign K s a • Pi.single (cyclePerm s a) 1 := by
  change (((chainPrefix K (s + 1)).val : Mat K (s + 2)) *
      ((simpleWeyl K (s + 2) (Fin.last (s + 1))).val : Mat K (s + 2))) *ᵥ Pi.single a 1 = _
  rw [← Matrix.mulVec_mulVec]
  change ((chainPrefix K (s + 1)).val : Mat K (s + 2)) *ᵥ
    (((simpleWeyl K (s + 2) (CFSGOrthogonalDGenerationForkTorus.last s)).val : Mat K (s + 2)) *ᵥ
      Pi.single a 1) = _
  rw [fork_basis K s a, Matrix.mulVec_smul,
    chainPrefix_basis K (s + 1) (forkPerm s a), smul_smul]
  rfl

theorem coxeter_monomial (s : ℕ) :
    ((coxeterWeyl K (s + 1)).val : Mat K (s + 2)) =
      monomial (cyclePerm s).symm (coxeterColumnSign K s ∘ (cyclePerm s).symm) := by
  ext i j
  have hh := congrArg (fun v : Index (s + 2) → K => v i) (coxeter_basis K s j)
  simp only [Matrix.mulVec_single_one, Matrix.col_apply] at hh
  by_cases hi : i = cyclePerm s j
  · subst i
    simpa [monomial_apply] using hh
  · have hi' : (cyclePerm s).symm i ≠ j := by
      intro he
      apply hi
      exact ((cyclePerm s).apply_symm_apply i).symm.trans (congrArg (cyclePerm s) he)
    simpa [monomial_apply, hi', Pi.single_apply, hi, Ne.symm hi] using hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationCoxeterMonomial
