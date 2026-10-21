import SymmetricSubgroupAsymptotics.S8Seed29NormalizerRoots
import SymmetricSubgroupAsymptotics.FiniteSubgroupJoinWords
import Mathlib.Tactic.FinCases

/-! Eight literal low-row candidates above original8T29. Each generator
tuple is an actual root adjunction or its displayed normalizer image.
This definition makes no completeness or numerical order assertion. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed29LowModels
open S8Seed29LeftCosets

def rootGenerators (k : Fin 32) : Fin 6 → Ambient :=
  Matrix.vecCons (representatives (S8Seed29NormalizerRoots.roots k))
    BinaryMenuCayley8T29.generators

def generators : Fin 8 → Fin 6 → Ambient :=
  ![rootGenerators 0, rootGenerators 3, rootGenerators 4, rootGenerators 10,
    rootGenerators 17, rootGenerators 30,
    (fun j => (MulAut.conj S8Seed29NormalizerRoots.normalizer) (rootGenerators 3 j)),
    (fun j => (MulAut.conj S8Seed29NormalizerRoots.normalizer) (rootGenerators 17 j))]

def rows (i : Fin 8) : Subgroup Ambient := Subgroup.closure (Set.range (generators i))

theorem root_closure (k : Fin 32) : Subgroup.closure (Set.range (rootGenerators k)) =
    H ⊔ Subgroup.closure {representatives (S8Seed29NormalizerRoots.roots k)} := by
  simp only [rootGenerators, Matrix.range_cons, Subgroup.closure_union, sup_comm]

theorem rows_zero : rows 0 = H := by
  change Subgroup.closure (Set.range (rootGenerators 0)) = H
  rw [root_closure, S8Seed29NormalizerRoots.root_zero_eq_seed]

theorem normalizer_sq : S8Seed29NormalizerRoots.normalizer *
    S8Seed29NormalizerRoots.normalizer = 1 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

end SymmetricSubgroupAsymptotics.S8Seed29LowModels
end
