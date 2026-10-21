import SymmetricSubgroupAsymptotics.S8Seed18NormalizerRoots
import SymmetricSubgroupAsymptotics.FiniteSubgroupJoinWords
import Mathlib.Tactic.FinCases

/-! Four literal low candidates above original8T18. They are the actual
seed and three displayed root adjunctions; this asserts no completeness. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.S8Seed18LowModels
open S8Seed18LeftCosets

def rootGenerators (k : Fin 66) : Fin 6 → Ambient :=
  Matrix.vecCons (representatives (S8Seed18NormalizerRoots.roots k))
    BinaryMenuCayley8T18.generators

def generators : Fin 4 → Fin 6 → Ambient :=
  ![rootGenerators 0, rootGenerators 12, rootGenerators 43, rootGenerators 52]

def rows (i : Fin 4) : Subgroup Ambient := Subgroup.closure (Set.range (generators i))

theorem root_closure (k : Fin 66) : Subgroup.closure (Set.range (rootGenerators k)) =
    H ⊔ Subgroup.closure {representatives (S8Seed18NormalizerRoots.roots k)} := by
  simp only [rootGenerators, Matrix.range_cons, Subgroup.closure_union, sup_comm]

theorem rows_zero : rows 0 = H := by
  change Subgroup.closure (Set.range (rootGenerators 0)) = H
  rw [root_closure, S8Seed18NormalizerRoots.root_zero_eq_seed]

theorem seed_le_root (k : Fin 66) : H ≤ Subgroup.closure (Set.range (rootGenerators k)) := by
  rw [root_closure]
  exact le_sup_left

theorem seed_le (i : Fin 4) : H ≤ rows i := by
  fin_cases i
  · exact seed_le_root 0
  · exact seed_le_root 12
  · exact seed_le_root 43
  · exact seed_le_root 52

end SymmetricSubgroupAsymptotics.S8Seed18LowModels
end
