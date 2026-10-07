import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleRegistryJoinData

/-! Selected invariant-state cyclic joins 16–31. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleRegistry

local instance sourceGroupJoin16 : Group Source := PrimitiveAffineEightFrameRow20TopCertificate.group
local instance sourceInhabitedJoin16 : Inhabited Source := ⟨1⟩

namespace JoinChunk16

def embed (i : Fin 16) : Fin 49 :=
  ⟨16 + i.val, by omega⟩

private theorem old_mem_child : ∀ i : Fin 16, ∀ c j,
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 16, ∀ c,
    PrimitiveAffineEightFrameRow20ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow20ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 16, ∀ c j,
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates (embed i) c j) +
        ((childOrbitWords (embed i) c j).map (fun g ↦
          PrimitiveAffineEightFrameRow20ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow20ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;> native_decide +revert

theorem child_eq (i : Fin 16) (c : Fin 40) :
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow20ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow20ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow20ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow20ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow20ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow20ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates (embed i) c) (childOrbitWords (embed i) c)
    (child_basis_eq i c)

end JoinChunk16

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ModuleRegistry

end
