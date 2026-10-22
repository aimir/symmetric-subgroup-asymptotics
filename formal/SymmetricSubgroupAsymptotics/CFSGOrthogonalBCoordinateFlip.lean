import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationShortMembership

/-! Actual coordinate-pair flips in the original B matrix group. The
three quadratic short-root words are retained, including the middle
coordinate and both second-degree coefficients. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBCoordinateFlip
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationShortArrays
open CFSGOrthogonalBGenerationShortMembership
variable (K : Type) [Field K]

def flip (r : ℕ) (i : Fin (r+1)) : elementaryRootGroup K (r+1) :=
  ⟨shortUnit K (r+1) (Sum.inl i) (-1) * shortUnit K (r+1) (Sum.inr i) (-1) *
      shortUnit K (r+1) (Sum.inl i) (-1),
    (elementaryRootGroup K (r+1)).mul_mem
      ((elementaryRootGroup K (r+1)).mul_mem
        (shortUnit_mem K r (Sum.inl i) (-1)) (shortUnit_mem K r (Sum.inr i) (-1)))
      (shortUnit_mem K r (Sum.inl i) (-1))⟩

def flipArray (r : ℕ) (i : Fin (r+1)) : Mat K (r+1) :=
  1 - Matrix.single (pos (r+1) i) (pos (r+1) i) 1 -
    Matrix.single (neg (r+1) i) (neg (r+1) i) 1 -
    Matrix.single (middle (r+1)) (middle (r+1)) 2 -
    Matrix.single (pos (r+1) i) (neg (r+1) i) 1 -
    Matrix.single (neg (r+1) i) (pos (r+1) i) 1

set_option maxHeartbeats 600000 in
theorem flip_val (r : ℕ) (i : Fin (r+1)) :
    ((flip K r i).val : Mat K (r+1)) = flipArray K r i := by
  change (shortUnit K (r+1) (Sum.inl i) (-1) : Mat K (r+1)) *
    (shortUnit K (r+1) (Sum.inr i) (-1) : Mat K (r+1)) *
    (shortUnit K (r+1) (Sum.inl i) (-1) : Mat K (r+1)) = _
  simp [shortArray, shortSecond, paired, flipArray, pos,
    CFSGOrthogonalBSerreMatrices.neg, middle, mul_add, add_mul, mul_sub, sub_mul]
  all_goals ext x y
  all_goals simp [Matrix.single]
  all_goals try split_ifs
  all_goals ring

theorem flip_basis (r : ℕ) (i : Fin (r+1)) (x : Index (r+1)) :
    ((flip K r i).val : Mat K (r+1)) *ᵥ Pi.single x 1 =
      (if x=pos (r+1) i ∨ x=neg (r+1) i ∨ x=middle (r+1) then (-1:K) else 1) •
        Pi.single (Equiv.swap (pos (r+1) i) (neg (r+1) i) x) 1 := by
  rw [flip_val, Matrix.mulVec_single_one]
  funext y
  by_cases hp : x=pos (r+1) i
  · subst x
    simp [flipArray, Matrix.col_apply, Matrix.single_apply, Matrix.one_apply,
      Pi.single_apply, pos, CFSGOrthogonalBSerreMatrices.neg, middle, eq_comm]
    all_goals try split_ifs
    all_goals ring
  · by_cases hn : x=neg (r+1) i
    · subst x
      simp [flipArray, Matrix.col_apply, Matrix.single_apply, Matrix.one_apply,
        Pi.single_apply, pos, CFSGOrthogonalBSerreMatrices.neg, middle, eq_comm]
      all_goals try split_ifs
      all_goals ring
    · by_cases hm : x=middle (r+1)
      · rw [Equiv.swap_apply_of_ne_of_ne hp hn]
        subst x
        simp [flipArray, Matrix.col_apply, Matrix.single_apply, Matrix.one_apply,
          Pi.single_apply, pos, CFSGOrthogonalBSerreMatrices.neg, middle, eq_comm]
        all_goals try split_ifs
        all_goals ring
      · rw [Equiv.swap_apply_of_ne_of_ne hp hn]
        simp [flipArray, Matrix.col_apply, Matrix.one_apply,
          Pi.single_apply, hp, hn, hm, Ne.symm hp, Ne.symm hn, Ne.symm hm, eq_comm]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBCoordinateFlip
