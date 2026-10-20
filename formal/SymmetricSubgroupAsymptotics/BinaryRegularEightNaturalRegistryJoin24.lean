import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryCharts

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistry.Join24

def embed (i : Fin 12) : Fin 47 := ⟨24 + i.val, by omega⟩
private theorem old_mem : ∀ i c j,
  (charts (embed i)).2.inclusion (Pi.single j 1) ∈ (charts (child (embed i) c)).2.space := by decide +kernel
private theorem representative_mem : ∀ i c,
  representative c ∈ (charts (child (embed i) c)).2.space := by decide +kernel
private theorem basis_eq : ∀ i c j,
  (charts (child (embed i) c)).2.inclusion (Pi.single j 1) =
    (charts (embed i)).2.inclusion (binaryVectorOfMask _ ((childOldMasks (embed i) c)[j.val]!)) +
      ((orbitList ((childOrbitMasks (embed i) c)[j.val]!)).map (fun g => rho g (representative c))).sum := by decide +kernel
theorem child_eq (i : Fin 12) (c : Fin 24) :
  (states (child (embed i) c)).toSubmodule =
    (states (embed i)).toSubmodule ⊔ binaryOrbitSpan rho (representative c) := by
  rw [states_space, states_space]
  exact binaryCoordinate_orbit_join_eq
    (charts (embed i)).2 (charts (child (embed i) c)).2 rho
    (states (child (embed i) c)) (states_space _) (representative c)
    (old_mem i c) (representative_mem i c)
    (fun j => binaryVectorOfMask _ ((childOldMasks (embed i) c)[j.val]!))
    (fun j => orbitList ((childOrbitMasks (embed i) c)[j.val]!)) (basis_eq i c)

end SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistry.Join24
