import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27ModuleRegistryJoinData

/-! Selected invariant-state cyclic joins 8–10. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27ModuleRegistry

local instance sourceGroupJoin8 : Group Source := PrimitiveAffineEightFrameRow27TopCertificate.group
local instance sourceInhabitedJoin8 : Inhabited Source := ⟨1⟩

namespace JoinChunk8

def embed (i : Fin 3) : Fin 11 :=
  ⟨8 + i.val, by omega⟩

private theorem old_mem_child : ∀ i : Fin 3, ∀ c j,
    (PrimitiveAffineEightFrameRow27ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow27ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 3, ∀ c,
    PrimitiveAffineEightFrameRow27ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow27ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 3, ∀ c j,
    (PrimitiveAffineEightFrameRow27ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates (embed i) c j) +
        ((childOrbitWords (embed i) c j).map (fun g ↦
          PrimitiveAffineEightFrameRow27ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow27ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;> native_decide +revert

theorem child_eq (i : Fin 3) (c : Fin 11) :
    (PrimitiveAffineEightFrameRow27ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow27ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow27ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow27ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow27ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow27ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow27ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow27ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow27ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow27ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates (embed i) c) (childOrbitWords (embed i) c)
    (child_basis_eq i c)

end JoinChunk8

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27ModuleRegistry

end
