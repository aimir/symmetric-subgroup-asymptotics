import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexMiddlePlane
import Mathlib.Tactic.FinCases

/-! The actual last-plane action of the U-normalizer is multiplicative.
Both flags used to construct it were reconstructed from the SAME U.
The action is not assumed to be orientation preserving. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexMiddleAction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexPrefixNormalizer CFSGOrthogonalDIndexPrefixPerpendicular
open CFSGOrthogonalDIndexMiddlePlane
variable (K : Type) [Field K]

def middleIndex (s : ℕ) (i : Fin 2) : Index (s + 4) :=
  if i = 0 then Sum.inl (lastIndex s) else Sum.inr (lastIndex s)

def middleMatrix (s : ℕ) (A : elementaryRootGroup K (s + 4)) : Matrix (Fin 2) (Fin 2) K :=
  fun i j => (A.val : Mat K (s + 4)) (middleIndex s i) (middleIndex s j)

theorem middleIndex_flag_bound (s : ℕ) (i : Fin 2) :
    s + 3 ≤ (flagEquiv (s + 4) (middleIndex s i)).val := by
  by_cases hi : i = 0
  · simp only [middleIndex, if_pos hi]
    change s + 3 ≤ s + 3
    exact le_rfl
  · simp only [middleIndex, if_neg hi]
    change s + 3 ≤ s + 4 + (Fin.rev (lastIndex s)).val
    omega

theorem middle_basis_perp (s : ℕ) (i : Fin 2) :
    Pi.single (middleIndex s i) (1 : K) ∈
      positivePerpendicular K (s + 4) (s + 3) := by
  by_cases hi : i = 0
  · simpa only [middleIndex, if_pos hi, middleCoordinate, Bool.false_eq_true, if_false]
      using middle_basis_perpendicular K s false
  · simpa only [middleIndex, if_neg hi, middleCoordinate, if_true]
      using middle_basis_perpendicular K s true

theorem middleMatrix_mul (s : ℕ) (A B : elementaryRootGroup K (s + 4))
    (hA : A ∈ Subgroup.normalizer
      (unipotent K (s + 4) : Set (elementaryRootGroup K (s + 4))))
    (hB : B ∈ Subgroup.normalizer
      (unipotent K (s + 4) : Set (elementaryRootGroup K (s + 4)))) :
    middleMatrix K s (A * B) = middleMatrix K s A * middleMatrix K s B := by
  ext i j
  have hp : (∑ k : Fin (s + 4),
      (A.val : Mat K (s + 4)) (middleIndex s i) (Sum.inl k) *
        (B.val : Mat K (s + 4)) (Sum.inl k) (middleIndex s j)) =
      (A.val : Mat K (s + 4)) (middleIndex s i) (Sum.inl (lastIndex s)) *
        (B.val : Mat K (s + 4)) (Sum.inl (lastIndex s)) (middleIndex s j) := by
    apply Finset.sum_eq_single (lastIndex s)
    · intro k _ hkl
      have hlt : k.val < s + 3 := by
        have hb := k.isLt
        have hn : k.val ≠ s + 3 := fun h => hkl (Fin.ext h)
        omega
      have hz := normalizer_positive_column_zero K s A hA k (by omega) (middleIndex s i)
        (by have hb := middleIndex_flag_bound s i; omega)
      rw [hz, zero_mul]
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  have hn : (∑ k : Fin (s + 4),
      (A.val : Mat K (s + 4)) (middleIndex s i) (Sum.inr k) *
        (B.val : Mat K (s + 4)) (Sum.inr k) (middleIndex s j)) =
      (A.val : Mat K (s + 4)) (middleIndex s i) (Sum.inr (lastIndex s)) *
        (B.val : Mat K (s + 4)) (Sum.inr (lastIndex s)) (middleIndex s j) := by
    have hcol := normalizer_preserves_positivePerpendicular K s B hB (s + 3) (by omega)
      _ (middle_basis_perp K s j)
    apply Finset.sum_eq_single (lastIndex s)
    · intro k _ hkl
      have hlt : k.val < s + 3 := by
        have hb := k.isLt
        have hne : k.val ≠ s + 3 := fun h => hkl (Fin.ext h)
        omega
      have hz := hcol k hlt
      change ((B.val : Mat K (s + 4)) *ᵥ Pi.single (middleIndex s j) 1) (Sum.inr k) = 0 at hz
      rw [Matrix.mulVec_single_one] at hz
      change (B.val : Mat K (s + 4)) (Sum.inr k) (middleIndex s j) = 0 at hz
      rw [hz, mul_zero]
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  change ((A.val : Mat K (s + 4)) * (B.val : Mat K (s + 4)))
    (middleIndex s i) (middleIndex s j) = _
  rw [Matrix.mul_apply, Fintype.sum_sum_type, hp, hn, Matrix.mul_apply, Fin.sum_univ_two]
  rfl

def rootNormalizer (s : ℕ) : Subgroup (elementaryRootGroup K (s + 4)) :=
  Subgroup.normalizer
    (unipotent K (s + 4) : Set (elementaryRootGroup K (s + 4)))

def middleHom (s : ℕ) : rootNormalizer K s →* Matrix (Fin 2) (Fin 2) K where
  toFun A := middleMatrix K s A.val
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [middleMatrix, middleIndex]
  map_mul' A B := middleMatrix_mul K s A.val B.val A.property B.property

theorem middle_matrix_dichotomy (s : ℕ) (A : rootNormalizer K s) :
    ((middleHom K s A) 0 1 = 0 ∧ (middleHom K s A) 1 0 = 0 ∧
        (middleHom K s A) 0 0 * (middleHom K s A) 1 1 = 1) ∨
      ((middleHom K s A) 0 0 = 0 ∧ (middleHom K s A) 1 1 = 0 ∧
        (middleHom K s A) 0 1 * (middleHom K s A) 1 0 = 1) := by
  exact hyperbolic_plane_dichotomy K _ _ _ _
    (normalizer_middle_column_product K s A.val A.property false)
    (normalizer_middle_column_product K s A.val A.property true)
    (normalizer_middle_cross_product K s A.val A.property)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexMiddleAction
