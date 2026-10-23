import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Rank-one decomposition of literal two-by-two Hermitian matrices.
The diagonal coefficient belongs to the fixed field by the displayed
entry equation. This works in characteristic two and requires neither
norm surjectivity nor a classification of any classical group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
variable {K : Type*} [Field K]

def Hermitian (sigma : K ≃+* K) (A : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∀ i j, sigma (A j i) = A i j

def rankOne (sigma : K ≃+* K) (a : K) (v : Fin 2 → K) : Matrix (Fin 2) (Fin 2) K :=
  fun i j => a * v i * sigma (v j)

theorem rankOne_hermitian (sigma : K ≃+* K) (hsigma : ∀ a, sigma (sigma a) = a)
    (a : K) (ha : sigma a = a) (v : Fin 2 → K) : Hermitian sigma (rankOne sigma a v) := by
  intro i j
  simp only [rankOne, map_mul, ha, hsigma]
  ring

theorem rankOne_det (sigma : K ≃+* K) (a : K) (v : Fin 2 → K) :
    (rankOne sigma a v).det = 0 := by
  rw [Matrix.det_fin_two]
  simp only [rankOne]
  ring

theorem hermitian_det_zero_rankOne (sigma : K ≃+* K)
    (A : Matrix (Fin 2) (Fin 2) K) (hA : Hermitian sigma A)
    (hdet : A.det = 0) (hne : A ≠ 0) :
    ∃ (a : K) (v : Fin 2 → K), a ≠ 0 ∧ sigma a = a ∧ v ≠ 0 ∧ A = rankOne sigma a v := by
  have h00 : sigma (A 0 0) = A 0 0 := hA 0 0
  have h10 : sigma (A 1 0) = A 0 1 := hA 0 1
  have h11 : sigma (A 1 1) = A 1 1 := hA 1 1
  rw [Matrix.det_fin_two] at hdet
  by_cases ha : A 0 0 = 0
  · have hprod : A 0 1 * A 1 0 = 0 := by simpa only [ha, zero_mul, zero_sub, neg_eq_zero] using hdet
    have h01 : A 0 1 = 0 := by
      rcases mul_eq_zero.mp hprod with h | h
      · exact h
      · rw [h, map_zero] at h10
        exact h10.symm
    have h10zero : A 1 0 = 0 := (map_eq_zero sigma).mp (h10.trans h01)
    have hn : A 1 1 ≠ 0 := by
      intro h
      apply hne
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, h01, h10zero, h]
    refine ⟨A 1 1, ![0, 1], hn, h11, ?_, ?_⟩
    · intro h
      have he := congrFun h (1 : Fin 2)
      exact one_ne_zero he
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [rankOne, ha, h01, h10zero]
  · have hratio : sigma (A 1 0 / A 0 0) = A 0 1 / A 0 0 := by
      rw [map_div₀, h10, h00]
    have hlast : A 1 1 = A 1 0 * A 0 1 / A 0 0 := by
      apply (eq_div_iff ha).mpr
      calc
        A 1 1 * A 0 0 = A 0 0 * A 1 1 := mul_comm _ _
        _ = A 0 1 * A 1 0 := sub_eq_zero.mp hdet
        _ = A 1 0 * A 0 1 := mul_comm _ _
    refine ⟨A 0 0, ![1, A 1 0 / A 0 0], ha, h00, ?_, ?_⟩
    · intro h
      have he := congrFun h (0 : Fin 2)
      exact one_ne_zero he
    · ext i j
      fin_cases i <;> fin_cases j
      · simp [rankOne]
      · change A 0 1 = A 0 0 * 1 * sigma (A 1 0 / A 0 0)
        rw [hratio, mul_one]
        field_simp [ha] <;> ring
      · change A 1 0 = A 0 0 * (A 1 0 / A 0 0) * sigma 1
        rw [map_one, mul_one]
        field_simp [ha] <;> ring
      · change A 1 1 = A 0 0 * (A 1 0 / A 0 0) * sigma (A 1 0 / A 0 0)
        rw [hratio, hlast]
        field_simp [ha] <;> ring

end SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
