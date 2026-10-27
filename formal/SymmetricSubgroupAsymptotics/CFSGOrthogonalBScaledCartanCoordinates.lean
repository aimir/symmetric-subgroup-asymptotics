import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntegralParityCoordinates

/-! Twice the inverse simple-coroot coordinate map is INTEGER-valued on
all matrices. Proper-prefix diagonal sums get coefficient two; the
terminal coordinate is the full positive trace. This is an actual
uniform formula for the pinned B coroots, not a determinant assertion. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBScaledCartanCoordinates
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBIntegralParityCoordinates
variable (R : Type*) [CommRing R] (r : ℕ)

def prefixTrace (i : Fin r) : Mat R r →ₗ[R] R where
  toFun M := ∑ k : Fin r, if k.val ≤ i.val then M (pos r k) (pos r k) else 0
  map_add' M N := by
    simp only [Matrix.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs <;> simp
  map_smul' a M := by
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs <;> simp

theorem prefixTrace_single_pos (i j : Fin r) (a : R) :
    prefixTrace R r i (Matrix.single (pos r j) (pos r j) a) =
      if j.val ≤ i.val then a else 0 := by
  change (∑ k : Fin r, if k.val ≤ i.val then
    Matrix.single (pos r j) (pos r j) a (pos r k) (pos r k) else 0) = _
  have ht (k : Fin r) : (if k.val ≤ i.val then
      Matrix.single (pos r j) (pos r j) a (pos r k) (pos r k) else 0) =
      if j = k then (if j.val ≤ i.val then a else 0) else 0 := by
    by_cases he : j = k
    · subst k; simp
    · simp [Matrix.single_apply, pos, he, Ne.symm he]
  simp_rw [ht]
  simp [eq_comm]

theorem prefixTrace_single_neg (i j : Fin r) (a : R) :
    prefixTrace R r i (Matrix.single (neg r j) (neg r j) a) = 0 := by
  simp [prefixTrace, Matrix.single, pos, neg]

theorem prefixTrace_cartan (i j : Fin r) :
    prefixTrace R r i (cartan R r j) =
      if j.val + 1 < r then
        (if j.val ≤ i.val then 1 else 0) - (if j.val + 1 ≤ i.val then 1 else 0)
      else if j.val ≤ i.val then 2 else 0 := by
  rw [cartan_eq]
  by_cases hj : j.val + 1 < r
  · simp only [dif_pos hj, if_pos hj, map_sub, map_add,
      prefixTrace_single_pos, prefixTrace_single_neg, zero_add, add_zero, Fin.val_mk]
  · simp only [dif_neg hj, if_neg hj, map_sub, prefixTrace_single_pos,
      prefixTrace_single_neg, sub_zero]

def doubledCoordinates : Mat R r →ₗ[R] (Fin r → R) where
  toFun M i := if i.val + 1 < r then 2 * prefixTrace R r i M else positiveTrace R r M
  map_add' M N := by
    funext i
    by_cases h : i.val + 1 < r <;> simp [h, map_add, mul_add]
  map_smul' a M := by
    funext i
    by_cases h : i.val + 1 < r <;> simp [h, map_smul, smul_eq_mul] <;> ring

theorem doubledCoordinates_cartan (j : Fin r) :
    doubledCoordinates R r (cartan R r j) = (2 : R) • Pi.single j 1 := by
  funext i
  change (if i.val + 1 < r then 2 * prefixTrace R r i (cartan R r j)
    else positiveTrace R r (cartan R r j)) = ((2 : R) • Pi.single j 1) i
  rw [prefixTrace_cartan, positiveTrace_cartan]
  by_cases hi : i.val + 1 < r
  · by_cases hj : j.val + 1 < r
    · by_cases hij : j = i
      · subst j
        simp [hi, Pi.single_apply]
      · have hji : j.val ≠ i.val := fun he => hij (Fin.ext he)
        by_cases hle : j.val ≤ i.val
        · have hle' : j.val + 1 ≤ i.val := by omega
          simp [hi, hj, hle, hle', Pi.single_apply, hij, Ne.symm hij]
        · have hle' : ¬ j.val + 1 ≤ i.val := by omega
          simp [hi, hj, hle, hle', Pi.single_apply, hij, Ne.symm hij]
    · have hji : ¬ j.val ≤ i.val := by have hjlt := j.isLt; omega
      have hne : j ≠ i := by intro he; subst j; omega
      simp [hi, hj, hji, Pi.single_apply, hne, Ne.symm hne]
  · by_cases hj : j.val + 1 < r
    · have hne : j ≠ i := by intro he; subst j; omega
      simp [hi, hj, Pi.single_apply, hne, Ne.symm hne]
    · have he : j = i := by
        apply Fin.ext
        have hilt := i.isLt
        have hjlt := j.isLt
        omega
      subst j
      simp [hi, Pi.single_apply]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBScaledCartanCoordinates
