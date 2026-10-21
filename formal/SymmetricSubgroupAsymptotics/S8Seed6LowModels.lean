import SymmetricSubgroupAsymptotics.S8Seed6NormalizerRoots
import SymmetricSubgroupAsymptotics.FiniteSubgroupJoinWords
import Mathlib.Tactic.FinCases

/-! The seed and two literal low candidates above original8T6. This module
defines actual root adjunctions and proves inclusions; it assumes no coverage. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.S8Seed6LowModels
open S8Seed6LeftCosets

def rootGenerators (k : Fin 108) : Fin 3 → Ambient :=
  Matrix.vecCons (representatives (S8Seed6NormalizerRoots.roots k))
    BinaryMenuCayley8T6.generators

def generators : Fin 3 → Fin 3 → Ambient :=
  ![rootGenerators 0, rootGenerators 37, rootGenerators 71]

def rows (i : Fin 3) : Subgroup Ambient := Subgroup.closure (Set.range (generators i))

theorem root_closure (k : Fin 108) : Subgroup.closure (Set.range (rootGenerators k)) =
    H ⊔ Subgroup.closure {representatives (S8Seed6NormalizerRoots.roots k)} := by
  simp only [rootGenerators, Matrix.range_cons, Subgroup.closure_union, sup_comm]

theorem rows_zero : rows 0 = H := by
  change Subgroup.closure (Set.range (rootGenerators 0)) = H
  rw [root_closure, S8Seed6NormalizerRoots.root_zero_eq_seed]

theorem seed_le_root (k : Fin 108) : H ≤ Subgroup.closure (Set.range (rootGenerators k)) := by
  rw [root_closure]
  exact le_sup_left

theorem seed_le (i : Fin 3) : H ≤ rows i := by
  fin_cases i
  · exact seed_le_root 0
  · exact seed_le_root 37
  · exact seed_le_root 71

end SymmetricSubgroupAsymptotics.S8Seed6LowModels
end
