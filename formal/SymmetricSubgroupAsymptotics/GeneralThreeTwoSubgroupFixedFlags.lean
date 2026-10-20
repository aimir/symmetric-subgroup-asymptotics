import SymmetricSubgroupAsymptotics.GeneralThreeTwoActualSubgroupCoverage
import SymmetricSubgroupAsymptotics.GeneralThreeTwoMatrixRows
import SymmetricSubgroupAsymptotics.BinaryThreeFixedSubgroups

/-! Twelve selected ordinary generator flag certificates in actual GL3(2).
The finite equations concern only3 generators and3 coordinates per row.
Generator closure proves each whole row has the stated invariant flag. -/

set_option autoImplicit false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupFixedFlags

open GeneralThreeTwoCayley GeneralThreeTwoMatrixRows
local instance : Group Source := group

private def dual : Fin 15 → Bool :=
  ![false, false, false, false, false, false, false, false,
    false, false, false, true, true, false, false]

private def vector : Fin 15 → BinaryThreeInvariantSubspaces.Vector :=
  ![![1,0,0], ![0,1,0], ![0,1,0], ![1,0,1], ![1,0,0],
    ![0,1,0], ![1,0,1], ![1,0,0], ![0,1,0], ![1,0,1],
    ![0,1,0], ![0,1,0], ![1,0,1], ![1,0,1], ![1,0,0]]

private theorem vector_ne_zero (i : Fin 15) : vector i ≠ 0 := by
  fin_cases i <;> decide +kernel

private theorem generator_checked (i : Fin 15) : i ≠ 4 → i ≠ 7 → i ≠ 14 →
    ∀ j : Fin 3,
      if dual i then
        vector i ᵥ* (matrixRows (GeneralThreeTwoSubgroupRows.generators i j).index).val = vector i
      else
        (matrixRows (GeneralThreeTwoSubgroupRows.generators i j).index).val *ᵥ vector i = vector i := by
  fin_cases i <;> decide +kernel

theorem row_flag (i : Fin 15) (h4 : i ≠ 4) (h7 : i ≠ 7) (h14 : i ≠ 14) :
    (∃ v : BinaryThreeInvariantSubspaces.Vector, v ≠ 0 ∧
      ∀ g ∈ GeneralThreeTwoActualSubgroupCoverage.rows i, g.val *ᵥ v = v) ∨
    (∃ l : BinaryThreeInvariantSubspaces.Vector, l ≠ 0 ∧
      ∀ g ∈ GeneralThreeTwoActualSubgroupCoverage.rows i, l ᵥ* g.val = l) := by
  have hgen := generator_checked i h4 h7 h14
  cases hd : dual i with
  | false =>
    left
    refine ⟨vector i, vector_ne_zero i, ?_⟩
    have hfix := BinaryThreeInvariantSubspaces.generators_fix_vector
      matrixEquiv.toMonoidHom (GeneralThreeTwoSubgroupRows.generators i) (vector i)
      (fun j => by
        change (matrixEquiv (GeneralThreeTwoSubgroupRows.generators i j)).val *ᵥ vector i = vector i
        rw [matrixEquiv_apply]
        simpa only [hd, Bool.false_eq_true, ↓reduceIte] using hgen j)
    rintro g ⟨s, hs, rfl⟩
    exact hfix s hs
  | true =>
    right
    refine ⟨vector i, vector_ne_zero i, ?_⟩
    have hfix := BinaryThreeInvariantSubspaces.generators_fix_covector
      matrixEquiv.toMonoidHom (GeneralThreeTwoSubgroupRows.generators i) (vector i)
      (fun j => by
        change vector i ᵥ* (matrixEquiv (GeneralThreeTwoSubgroupRows.generators i j)).val = vector i
        rw [matrixEquiv_apply]
        simpa only [hd, ↓reduceIte] using hgen j)
    rintro g ⟨s, hs, rfl⟩
    exact hfix s hs

end SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupFixedFlags

end
