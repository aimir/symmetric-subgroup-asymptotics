import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleRegistryJoinData

/-! Selected invariant-state cyclic joins 32–47. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleRegistry

local instance sourceGroupJoin32 : Group Source := PrimitiveAffineEightFrameRow2TopCertificate.group
local instance sourceInhabitedJoin32 : Inhabited Source := ⟨1⟩

namespace JoinChunk32

def embed (i : Fin 16) : Fin 49 :=
  ⟨32 + i.val, by omega⟩

private theorem old_mem_child : ∀ i : Fin 16, ∀ c j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow2ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 16, ∀ c,
    PrimitiveAffineEightFrameRow2ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow2ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 16, ∀ c j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates (embed i) c j) +
        ((childOrbitWords (embed i) c j).map (fun g ↦
          PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow2ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;> native_decide +revert

theorem child_eq (i : Fin 16) (c : Fin 34) :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow2ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow2ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates (embed i) c) (childOrbitWords (embed i) c)
    (child_basis_eq i c)

end JoinChunk32

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleRegistry

end
