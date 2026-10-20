import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryCharts

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistry

def cyclicState (c : Fin 24) : Fin 47 := ⟨c.val, by omega⟩
private theorem point_mem : ∀ v : V, v ∈ (charts (cyclicState (pointClass v))).2.space := by decide +kernel
private theorem point_basis_eq : ∀ v : V, ∀ j,
  (charts (cyclicState (pointClass v))).2.inclusion (Pi.single j 1) =
    ((orbitList ((pointOrbitMasks v)[j.val]!)).map (fun g => rho g v)).sum := by decide +kernel
theorem point_span (v : V) :
  (states (cyclicState (pointClass v))).toSubmodule = binaryOrbitSpan rho v := by
  rw [states_space]
  apply le_antisymm
  · apply (charts (cyclicState (pointClass v))).2.le_of_basis_mem
    intro j
    rw [point_basis_eq]
    apply (binaryOrbitSpan rho v).list_sum_mem
    intro x hx
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx
    exact Submodule.subset_span ⟨g, rfl⟩
  · apply binaryOrbitSpan_le rho (states (cyclicState (pointClass v)))
    exact point_mem v
private theorem pointClass_representative : ∀ c, pointClass (representative c) = c := by decide +kernel
theorem point_representative_span (v : V) :
  binaryOrbitSpan rho v = binaryOrbitSpan rho (representative (pointClass v)) := by
  rw [← point_span v, ← point_span (representative (pointClass v)), pointClass_representative]

end SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistry
