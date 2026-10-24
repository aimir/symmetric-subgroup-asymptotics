import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOddQuadraticForm
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBTailLinearExtension
import SymmetricSubgroupAsymptotics.CFSGQuadraticHyperbolicShear
import Mathlib.Tactic.FinCases

/-! The original odd-B first pair and actual tail are hyperbolic
coordinates for half the original Gram norm. The opposite coordinate
is twice the original negative head, so no factor two is suppressed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOddPoleCoordinates

open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBVectorCoordinates
open CFSGOrthogonalBTailCoordinates CFSGOrthogonalBOddQuadraticForm
variable (K : Type) [Field K]

def coordinates (n : ℕ) (v : Index (n + 1) → K) : K × ((Index n → K) × K) :=
  (v (pos (n + 1) 0), (tailRestriction K n v, 2 * v (neg (n + 1) 0)))

def fromCoordinates (n : ℕ) (x : K × ((Index n → K) × K)) : Index (n + 1) → K :=
  fun i => Sum.elim x.2.1 (fun j : Fin 2 => if j = 0 then x.1 else (2 : K)⁻¹ * x.2.2)
    ((tailEquiv n).symm i)

theorem from_coordinates (h2 : (2 : K) ≠ 0) (n : ℕ) (v : Index (n + 1) → K) :
    fromCoordinates K n (coordinates K n v) = v := by
  funext i
  obtain ⟨i, rfl⟩ := (tailEquiv n).surjective i
  cases i with
  | inl j =>
    simpa only [fromCoordinates, Equiv.symm_apply_apply, Sum.elim_inl] using
      (show tailRestriction K n v j = v (tailEquiv n (Sum.inl j)) from rfl)
  | inr j =>
    fin_cases j
    · simp [fromCoordinates, coordinates]
    · simp only [fromCoordinates, Equiv.symm_apply_apply, Sum.elim_inr,
        if_neg (by decide : (1 : Fin 2) ≠ 0)]
      change (2 : K)⁻¹ * (2 * v (neg (n + 1) 0)) = v (neg (n + 1) 0)
      rw [← mul_assoc, inv_mul_cancel₀ h2, one_mul]

theorem coordinates_from (h2 : (2 : K) ≠ 0) (n : ℕ) (x : K × ((Index n → K) × K)) :
    coordinates K n (fromCoordinates K n x) = x := by
  apply Prod.ext
  · simp [coordinates, fromCoordinates]
  · apply Prod.ext
    · funext i
      simp only [coordinates, tailRestriction, fromCoordinates, tailEquiv_symm_tailIndex,
        Sum.elim_inl]
    · change 2 * fromCoordinates K n x (neg (n + 1) 0) = x.2.2
      simp only [fromCoordinates, tailEquiv_symm_neg_zero, Sum.elim_inr]
      change (2 : K) * ((2 : K)⁻¹ * x.2.2) = x.2.2
      rw [← mul_assoc, mul_inv_cancel₀ h2, one_mul]

def coordinateEquiv (h2 : (2 : K) ≠ 0) (n : ℕ) :
    (Index (n + 1) → K) ≃ₗ[K] K × ((Index n → K) × K) where
  toFun := coordinates K n
  invFun := fromCoordinates K n
  left_inv := from_coordinates K h2 n
  right_inv := coordinates_from K h2 n
  map_add' v w := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · change 2 * (v (neg (n + 1) 0) + w (neg (n + 1) 0)) =
          2 * v (neg (n + 1) 0) + 2 * w (neg (n + 1) 0)
        ring
  map_smul' a v := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · change 2 * (a * v (neg (n + 1) 0)) = a * (2 * v (neg (n + 1) 0))
        ring

theorem gram_norm_coordinates (n : ℕ) (v : Index (n + 1) → K) :
    (gram K (n + 1)).toBilin' v v =
      4 * v (pos (n + 1) 0) * v (neg (n + 1) 0) +
        (gram K n).toBilin' (tailRestriction K n v) (tailRestriction K n v) := by
  rw [CFSGOrthogonalBVectorCoordinates.gram_norm_coordinates,
    CFSGOrthogonalBVectorCoordinates.gram_norm_coordinates, Fin.sum_univ_succ]
  simp only [positivePart, negativePart, tailRestriction, tailIndex, pos, neg, middle,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  ring

theorem quadratic_coordinates (h2 : (2 : K) ≠ 0) (n : ℕ) (v : Index (n + 1) → K) :
    quadratic K (n + 1) v =
      CFSGQuadraticHyperbolicShear.norm (quadratic K n) (coordinates K n v) := by
  rw [quadratic_apply, gram_norm_coordinates, CFSGQuadraticHyperbolicShear.norm,
    quadratic_apply]
  change (2 : K)⁻¹ * (4 * v (pos (n + 1) 0) * v (neg (n + 1) 0) +
      (gram K n).toBilin' (tailRestriction K n v) (tailRestriction K n v)) =
    v (pos (n + 1) 0) * (2 * v (neg (n + 1) 0)) +
      (2 : K)⁻¹ * (gram K n).toBilin' (tailRestriction K n v) (tailRestriction K n v)
  calc
    _ = ((2 : K)⁻¹ * 2) * (v (pos (n + 1) 0) * (2 * v (neg (n + 1) 0))) +
        (2 : K)⁻¹ * (gram K n).toBilin' (tailRestriction K n v) (tailRestriction K n v) := by ring
    _ = _ := by rw [inv_mul_cancel₀ h2, one_mul]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOddPoleCoordinates
