import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29ModuleRegistryJoinData

/-! Selected invariant-state cyclic joins 0–4. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29ModuleRegistry

local instance sourceGroupJoin0 : Group Source := PrimitiveAffineEightFrameRow29TopCertificate.group
local instance sourceInhabitedJoin0 : Inhabited Source := ⟨1⟩

namespace JoinChunk0

def embed (i : Fin 5) : Fin 5 :=
  ⟨0 + i.val, by omega⟩

private theorem old_mem_child : ∀ i : Fin 5, ∀ c j,
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow29ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 5, ∀ c,
    PrimitiveAffineEightFrameRow29ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow29ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 5, ∀ c j,
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates (embed i) c j) +
        ((childOrbitWords (embed i) c j).map (fun g ↦
          PrimitiveAffineEightFrameRow29ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow29ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;> native_decide +revert

theorem child_eq (i : Fin 5) (c : Fin 5) :
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow29ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow29ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow29ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow29ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow29ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates (embed i) c) (childOrbitWords (embed i) c)
    (child_basis_eq i c)

end JoinChunk0

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29ModuleRegistry

end
