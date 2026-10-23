import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination

/-! Coordinate classification of every linear map preserving the split
hyperbolic-plane norm xy. The genuine quadratic equation is retained in
characteristic two; determinant is not used to select a component. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGHyperbolicPlaneIsometries
variable {K : Type} [Field K]

theorem diagonal_or_antidiagonal (A : Matrix (Fin 2) (Fin 2) K)
    (hQ : ∀ v : Fin 2 → K, (A *ᵥ v) 0 * (A *ᵥ v) 1 = v 0 * v 1) :
    ∃ c : Kˣ,
      (A 0 0 = c ∧ A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 1 1 = (c : K)⁻¹) ∨
      (A 0 0 = 0 ∧ A 0 1 = c ∧ A 1 0 = (c : K)⁻¹ ∧ A 1 1 = 0) := by
  have h00 : A 0 0 * A 1 0 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hQ ![1, 0]
  have h11 : A 0 1 * A 1 1 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hQ ![0, 1]
  have hs : (A 0 0 + A 0 1) * (A 1 0 + A 1 1) = 1 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hQ ![1, 1]
  have hc : A 0 0 * A 1 1 + A 0 1 * A 1 0 = 1 := by
    linear_combination hs - h00 - h11
  by_cases ha : A 0 0 = 0
  · have hp : A 0 1 * A 1 0 = 1 := by simpa only [ha, zero_mul, zero_add] using hc
    have hb : A 0 1 ≠ 0 := by
      intro h
      rw [h, zero_mul] at hp
      exact zero_ne_one hp
    have hd : A 1 1 = 0 := (mul_eq_zero.mp h11).resolve_left hb
    have hi : A 1 0 = (A 0 1)⁻¹ := by
      apply (mul_left_cancel₀ hb)
      rw [hp, mul_inv_cancel₀ hb]
    refine ⟨Units.mk0 (A 0 1) hb, Or.inr ?_⟩
    exact ⟨ha, rfl, hi, hd⟩
  · have hz : A 1 0 = 0 := (mul_eq_zero.mp h00).resolve_left ha
    have hp : A 0 0 * A 1 1 = 1 := by simpa only [hz, mul_zero, add_zero] using hc
    have hd : A 1 1 ≠ 0 := by
      intro h
      rw [h, mul_zero] at hp
      exact zero_ne_one hp
    have hb : A 0 1 = 0 := (mul_eq_zero.mp h11).resolve_right hd
    have hi : A 1 1 = (A 0 0)⁻¹ := by
      apply (mul_left_cancel₀ ha)
      rw [hp, mul_inv_cancel₀ ha]
    refine ⟨Units.mk0 (A 0 0) ha, Or.inl ?_⟩
    exact ⟨rfl, hb, hz, hi⟩

end SymmetricSubgroupAsymptotics.CFSGHyperbolicPlaneIsometries
