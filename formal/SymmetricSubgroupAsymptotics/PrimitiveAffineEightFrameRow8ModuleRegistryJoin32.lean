import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleRegistryJoinData

/-! Selected invariant-state cyclic joins 32–39. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleRegistry

local instance sourceGroupJoin32 : Group Source := PrimitiveAffineEightFrameRow8TopCertificate.group
local instance sourceInhabitedJoin32 : Inhabited Source := ⟨1⟩

namespace JoinChunk32

def embed (i : Fin 8) : Fin 43 :=
  ⟨32 + i.val, by omega⟩

private theorem old_mem_child : ∀ i : Fin 8, ∀ c j,
    (PrimitiveAffineEightFrameRow8ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow8ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 8, ∀ c,
    PrimitiveAffineEightFrameRow8ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow8ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 8, ∀ c j,
    (PrimitiveAffineEightFrameRow8ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates (embed i) c j) +
        ((childOrbitWords (embed i) c j).map (fun g ↦
          PrimitiveAffineEightFrameRow8ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow8ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;> native_decide +revert

theorem child_eq (i : Fin 8) (c : Fin 40) :
    (PrimitiveAffineEightFrameRow8ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow8ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow8ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow8ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow8ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow8ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow8ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow8ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow8ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow8ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates (embed i) c) (childOrbitWords (embed i) c)
    (child_basis_eq i c)

end JoinChunk32

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ModuleRegistry

end
