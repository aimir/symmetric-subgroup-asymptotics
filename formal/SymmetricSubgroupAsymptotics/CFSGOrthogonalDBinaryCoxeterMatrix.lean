import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryForkAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryCyclePermutation
import SymmetricSubgroupAsymptotics.CFSGTypeAMonomialMatrices

/-! The actual binary D Coxeter matrix is its literal coordinate
permutation. This binds the original D word to the star-root orbit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix CharTwo
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryCoxeterMatrix
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDBinaryCyclePermutation CFSGMatrixPairRotation CFSGTypeAMonomialMatrices
variable {K : Type} [Field K] [CharP K 2]

private theorem rotation_binary_basis {I : Type*} [Fintype I] [DecidableEq I]
    (p q x : I) (hpq : p ≠ q) :
    rotation K p q *ᵥ Pi.single x 1 = Pi.single (Equiv.swap p q x) 1 := by
  by_cases hp : x = p
  · subst x
    rw [rotation_basis_left K p q hpq, Equiv.swap_apply_left]
  · by_cases hq : x = q
    · subst x
      rw [rotation_basis_right K p q hpq, Equiv.swap_apply_right]
      funext i
      exact CharTwo.neg_eq _
    · rw [rotation_basis_other K p q x hp hq, Equiv.swap_apply_of_ne_of_ne hp hq]

theorem fork_binary_basis (s : ℕ) (a : Index (s + 2)) :
    ((simpleWeyl K (s + 2) (Fin.last (s + 1))).val : Mat K (s + 2)) *ᵥ Pi.single a 1 =
      Pi.single (forkPerm s a) 1 := by
  rw [fork_rotations, ← Matrix.mulVec_mulVec,
    rotation_binary_basis _ _ _ (by intro h; cases h),
    rotation_binary_basis _ _ _ (by intro h; cases h)]
  rfl

theorem chainPrefix_binary_basis (r : ℕ) (a : Index (r + 1)) :
    ((chainPrefix K r).val : Mat K (r + 1)) *ᵥ Pi.single a 1 =
      Pi.single (Equiv.sumCongr (finRotate (r + 1)) (finRotate (r + 1)) a) 1 := by
  have hside (side : Bool) (i : Fin (r + 1)) :
      ((chainPrefix K r).val : Mat K (r + 1)) *ᵥ
          Pi.single (if side then Sum.inr i else Sum.inl i) 1 =
        Pi.single (if side then Sum.inr (finRotate (r + 1) i)
          else Sum.inl (finRotate (r + 1) i)) 1 := by
    have hh := CFSGSymplecticSerreMatrices.chainWeylPrefix_basis K r r le_rfl side i.val
      (Nat.le_of_lt_succ i.isLt)
    by_cases hi : i.val < r
    · let j : Fin (r + 1) := ⟨i.val + 1, Nat.succ_lt_succ hi⟩
      simp only [hi, if_true] at hh
      rw [CFSGSymplecticSerreMatrices.naturalCoordinateBasis_val K r side i,
        CFSGSymplecticSerreMatrices.naturalCoordinateBasis_val K r side j] at hh
      rw [finRotate_of_lt hi]
      exact hh
    · have he : i = Fin.last r := by
        apply Fin.ext
        have hb := i.isLt
        change i.val = r
        omega
      subst i
      simp only [Fin.val_last, lt_self_iff_false, if_false, if_true,
        CharTwo.neg_eq, one_pow, one_smul] at hh
      have hlast := CFSGSymplecticSerreMatrices.naturalCoordinateBasis_val K r side (Fin.last r)
      have hzero := CFSGSymplecticSerreMatrices.naturalCoordinateBasis_val K r side (0 : Fin (r + 1))
      change CFSGSymplecticSerreMatrices.naturalCoordinateBasis K r side r = _ at hlast
      change CFSGSymplecticSerreMatrices.naturalCoordinateBasis K r side 0 = _ at hzero
      rw [hlast, hzero] at hh
      rw [finRotate_last]
      exact hh
  cases a with
  | inl i => exact hside false i
  | inr i => exact hside true i

theorem coxeter_binary_basis (s : ℕ) (a : Index (s + 2)) :
    ((coxeterWeyl K (s + 1)).val : Mat K (s + 2)) *ᵥ Pi.single a 1 =
      Pi.single (cyclePerm s a) 1 := by
  change (((chainPrefix K (s + 1)).val : Mat K (s + 2)) *
      ((simpleWeyl K (s + 2) (Fin.last (s + 1))).val : Mat K (s + 2))) *ᵥ Pi.single a 1 = _
  rw [← Matrix.mulVec_mulVec, fork_binary_basis, chainPrefix_binary_basis]
  rfl

theorem coxeter_binary_monomial (s : ℕ) :
    ((coxeterWeyl K (s + 1)).val : Mat K (s + 2)) =
      monomial (cyclePerm s).symm (fun _ => 1) := by
  ext i j
  have hh := congrArg (fun v : Index (s + 2) → K => v i) (coxeter_binary_basis (K := K) s j)
  simp only [Matrix.mulVec_single_one, Matrix.col_apply] at hh
  by_cases hi : i = cyclePerm s j
  · subst i
    simpa [monomial_apply] using hh
  · have hi' : (cyclePerm s).symm i ≠ j := by
      intro he
      apply hi
      exact ((cyclePerm s).apply_symm_apply i).symm.trans (congrArg (cyclePerm s) he)
    simpa [monomial_apply, hi', Pi.single_apply, hi, Ne.symm hi] using hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryCoxeterMatrix
