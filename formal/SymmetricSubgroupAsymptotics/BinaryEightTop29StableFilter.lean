import SymmetricSubgroupAsymptotics.BinaryEightTop29CoordinateAction
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryCharts

/-! A small larger-top stability filter of the EXISTING47 regular module
spaces. It proves no new invariant-registry completeness and no head
assertion. Actual module stability supplies the finite predicate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryEightTop29StableFilter
open BinaryEightTop29CoordinateAction
open BinaryRegularEightNaturalRegistry (charts)

def stable (i : Fin 47) : Prop := ∀ g : Fin 5, ∀ j : Fin (charts i).1,
  rho (generators g) ((charts i).2.inclusion (Pi.single j 1)) ∈ (charts i).2.space
instance stable_decidable (i : Fin 47) : Decidable (stable i) :=
  inferInstanceAs (Decidable (∀ g : Fin 5, ∀ j : Fin (charts i).1,
    rho (generators g) ((charts i).2.inclusion (Pi.single j 1)) ∈ (charts i).2.space))

theorem stable_index (i : Fin 47) (hi : stable i) :
    i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 11 ∨ i = 22 ∨ i = 23 ∨
    i = 24 ∨ i = 30 ∨ i = 42 ∨ i = 45 ∨ i = 46 := by
  have hc : ∀ j : Fin 47, stable j →
      j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 11 ∨ j = 22 ∨ j = 23 ∨
      j = 24 ∨ j = 30 ∨ j = 42 ∨ j = 45 ∨ j = 46 := by decide +kernel
  exact hc i hi

theorem stable_of_actual_space (W : Subrepresentation rho) (i : Fin 47)
    (hW : W.toSubmodule = (charts i).2.space) : stable i := by
  intro g j
  rw [← hW]
  apply W.apply_mem_toSubmodule
  rw [hW]
  exact ⟨_, rfl⟩

end SymmetricSubgroupAsymptotics.BinaryEightTop29StableFilter
