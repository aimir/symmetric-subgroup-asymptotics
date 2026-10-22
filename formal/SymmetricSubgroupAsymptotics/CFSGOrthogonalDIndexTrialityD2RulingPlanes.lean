import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The two literal families of residual singular planes: matrices
with a fixed column line, and matrices with a fixed row line, pulled
back through the exact original quadratic coordinate equivalence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
variable (K : Type) [Field K]

def columnMap (u : Fin 2 → K) : (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun p i j := u i * p j
  map_add' p q := by ext i j; simp [mul_add]
  map_smul' a p := by ext i j; simp [mul_left_comm]

def rowMap (v : Fin 2 → K) : (Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun p i j := p i * v j
  map_add' p q := by ext i j; simp [add_mul]
  map_smul' a p := by ext i j; simp [mul_assoc]

def columnPlane (u : Fin 2 → K) := (columnMap K u).range
def rowPlane (v : Fin 2 → K) := (rowMap K v).range

theorem columnMap_injective (u : Fin 2 → K) (hu : u ≠ 0) : Function.Injective (columnMap K u) := by
  have hi : ∃ i, u i ≠ 0 := by
    by_contra hn
    simp only [not_exists, not_not] at hn
    exact hu (funext hn)
  obtain ⟨i, hi⟩ := hi
  intro p q he
  funext j
  have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A i j) he
  change u i * p j = u i * q j at hh
  exact mul_left_cancel₀ hi hh

theorem rowMap_injective (v : Fin 2 → K) (hv : v ≠ 0) : Function.Injective (rowMap K v) := by
  have hj : ∃ j, v j ≠ 0 := by
    by_contra hn
    simp only [not_exists, not_not] at hn
    exact hv (funext hn)
  obtain ⟨j, hj⟩ := hj
  intro p q he
  funext i
  have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A i j) he
  change p i * v j = q i * v j at hh
  exact mul_right_cancel₀ hj hh

theorem columnPlane_finrank (u : Fin 2 → K) (hu : u ≠ 0) :
    Module.finrank K (columnPlane K u) = 2 :=
  (LinearMap.finrank_range_of_inj (columnMap_injective K u hu)).trans (by simp)

theorem rowPlane_finrank (v : Fin 2 → K) (hv : v ≠ 0) :
    Module.finrank K (rowPlane K v) = 2 :=
  (LinearMap.finrank_range_of_inj (rowMap_injective K v hv)).trans (by simp)

theorem columnPlane_det_zero (u : Fin 2 → K) (A : Matrix (Fin 2) (Fin 2) K)
    (hA : A ∈ columnPlane K u) : Matrix.det A = 0 := by
  obtain ⟨p, rfl⟩ := hA
  rw [Matrix.det_fin_two]
  change (u 0 * p 0) * (u 1 * p 1) - (u 0 * p 1) * (u 1 * p 0) = 0
  ring

theorem rowPlane_det_zero (v : Fin 2 → K) (A : Matrix (Fin 2) (Fin 2) K)
    (hA : A ∈ rowPlane K v) : Matrix.det A = 0 := by
  obtain ⟨p, rfl⟩ := hA
  rw [Matrix.det_fin_two]
  change (p 0 * v 0) * (p 1 * v 1) - (p 0 * v 1) * (p 1 * v 0) = 0
  ring

def originalColumnPlane (u : Fin 2 → K) : Submodule K (Index 2 → K) :=
  (columnPlane K u).map (determinantCoordinates K).symm.toLinearMap

def originalRowPlane (v : Fin 2 → K) : Submodule K (Index 2 → K) :=
  (rowPlane K v).map (determinantCoordinates K).symm.toLinearMap

theorem originalColumnPlane_finrank (u : Fin 2 → K) (hu : u ≠ 0) :
    Module.finrank K (originalColumnPlane K u) = 2 :=
  ((determinantCoordinates K).symm.finrank_map_eq (columnPlane K u)).trans (columnPlane_finrank K u hu)

theorem originalRowPlane_finrank (v : Fin 2 → K) (hv : v ≠ 0) :
    Module.finrank K (originalRowPlane K v) = 2 :=
  ((determinantCoordinates K).symm.finrank_map_eq (rowPlane K v)).trans (rowPlane_finrank K v hv)

theorem originalColumnPlane_singular (u : Fin 2 → K) :
    ∀ x ∈ originalColumnPlane K u, splitQuadraticForm K 2 x = 0 := by
  rintro x ⟨A, hA, rfl⟩
  have hh := determinantCoordinates_det K ((determinantCoordinates K).symm A)
  rw [LinearEquiv.apply_symm_apply] at hh
  exact hh.symm.trans (columnPlane_det_zero K u A hA)

theorem originalRowPlane_singular (v : Fin 2 → K) :
    ∀ x ∈ originalRowPlane K v, splitQuadraticForm K 2 x = 0 := by
  rintro x ⟨A, hA, rfl⟩
  have hh := determinantCoordinates_det K ((determinantCoordinates K).symm A)
  rw [LinearEquiv.apply_symm_apply] at hh
  exact hh.symm.trans (rowPlane_det_zero K v A hA)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
