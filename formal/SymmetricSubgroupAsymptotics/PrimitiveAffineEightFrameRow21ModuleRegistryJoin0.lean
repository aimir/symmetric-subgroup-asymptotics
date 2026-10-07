import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow21ModuleRegistryJoinData

/-! Selected invariant-state cyclic joins 0–15. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow21ModuleRegistry

local instance sourceGroupJoin0 : Group Source := PrimitiveAffineEightFrameRow21TopCertificate.group
local instance sourceInhabitedJoin0 : Inhabited Source := ⟨1⟩

namespace JoinChunk0

def embed (i : Fin 16) : Fin 27 :=
  ⟨0 + i.val, by omega⟩

private theorem old_mem_child : ∀ i : Fin 16, ∀ c j,
    (PrimitiveAffineEightFrameRow21ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow21ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 16, ∀ c,
    PrimitiveAffineEightFrameRow21ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow21ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 16, ∀ c j,
    (PrimitiveAffineEightFrameRow21ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates (embed i) c j) +
        ((childOrbitWords (embed i) c j).map (fun g ↦
          PrimitiveAffineEightFrameRow21ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow21ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;> native_decide +revert

theorem child_eq (i : Fin 16) (c : Fin 22) :
    (PrimitiveAffineEightFrameRow21ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow21ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow21ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow21ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow21ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow21ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow21ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow21ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow21ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow21ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates (embed i) c) (childOrbitWords (embed i) c)
    (child_basis_eq i c)

end JoinChunk0

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow21ModuleRegistry

end
