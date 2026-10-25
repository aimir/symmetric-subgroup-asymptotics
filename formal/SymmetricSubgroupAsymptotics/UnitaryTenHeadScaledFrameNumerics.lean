import Mathlib.Data.Nat.Log
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-! Ten rank/field parameter capacities, after a shared Hermitian frame
bound and determinant saving. This is arithmetic only: none of the
displayed ceilings is asserted here for an actual group or action. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.UnitaryTenHeadScaledFrameNumerics

def parameters : Fin 10 → ℕ × ℕ :=
  ![(2,3),(2,4),(2,5),(2,7),(2,8),(2,9),(3,2),(3,3),(3,4),(4,2)]

def indexFloor : Fin 10 → ℕ := ![27,40,50,343,64,270,27,48,64,48]

def orderCeiling (j : Fin 10) : ℕ :=
  3*(parameters j).2^(((parameters j).1+1)^2)/((parameters j).2+1)

def outerCeiling (j : Fin 10) : ℕ :=
  if parameters j=(3,2) then 2 else
    2*((parameters j).1+1)*Nat.log 2 (parameters j).2

theorem indexFloor_pos (j : Fin 10) : 0 < indexFloor j := by
  fin_cases j <;> decide +kernel

theorem parameter_admissible (j : Fin 10) :
    2 ≤ (parameters j).1 ∧ 2 ≤ (parameters j).2 ∧
      ((parameters j).1=2 → (parameters j).2≠2) := by
  fin_cases j <;> decide +kernel

/-- Exhaust the small rank/field complement without importing a group
classification or the downstream small-fibre owner interface. -/
theorem parameter_of_not_tail (r q : ℕ) (hr : 2 ≤ r) (hq : 2 ≤ q)
    (hsmall : r=2 → q≠2) (h6 : q≠6) (h10 : q≠10)
    (hlow : ¬((r=2 ∧ 11 ≤ q) ∨ (r=3 ∧ 5 ≤ q)))
    (hhigh : ¬(4 ≤ r ∧ (r=4 → 3 ≤ q))) :
    ∃ j : Fin 10, parameters j=(r,q) := by
  have hrange : r=2 ∨ r=3 ∨ r=4 := by omega
  rcases hrange with rfl | rfl | rfl
  · have hqrange : q=3 ∨ q=4 ∨ q=5 ∨ q=7 ∨ q=8 ∨ q=9 := by
      have := hsmall rfl
      omega
    rcases hqrange with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
    · exact ⟨4,rfl⟩
    · exact ⟨5,rfl⟩
  · have hqrange : q=2 ∨ q=3 ∨ q=4 := by omega
    rcases hqrange with rfl | rfl | rfl
    · exact ⟨6,rfl⟩
    · exact ⟨7,rfl⟩
    · exact ⟨8,rfl⟩
  · have he : q=2 := by omega
    subst q
    exact ⟨9,rfl⟩

theorem scaled_capacity (j : Fin 10) :
    25*((orderCeiling j/indexFloor j+1)*outerCeiling j)^3 ≤ 3^indexFloor j := by
  fin_cases j <;> decide +kernel

theorem scaled_capacity_of_bounds (j : Fin 10) (k o d : ℕ)
    (hk : k ≤ orderCeiling j/indexFloor j+1) (ho : o ≤ outerCeiling j)
    (hd : indexFloor j ≤ d) : 25*(k*o)^3 ≤ 3^d :=
  ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.mul_le_mul hk ho) 3)).trans
    (scaled_capacity j)).trans (Nat.pow_le_pow_right (by decide) hd)

end SymmetricSubgroupAsymptotics.UnitaryTenHeadScaledFrameNumerics
