import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistryJoinData

/-! Selected invariant-state cyclic joins 64–71. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistry

local instance sourceGroupJoin64 : Group Source := PrimitiveAffineEightFrameRow0TopCertificate.group
local instance sourceInhabitedJoin64 : Inhabited Source := ⟨1⟩

namespace JoinChunk64

def embed (i : Fin 8) : Fin 101 :=
  ⟨64 + i.val, by omega⟩

private theorem old_mem_child : ∀ i : Fin 8, ∀ c j,
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 8, ∀ c,
    PrimitiveAffineEightFrameRow0ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow0ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 8, ∀ c j,
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates (embed i) c j) +
        ((childOrbitWords (embed i) c j).map (fun g ↦
          PrimitiveAffineEightFrameRow0ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow0ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;> native_decide +revert

theorem child_eq (i : Fin 8) (c : Fin 67) :
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow0ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow0ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow0ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow0ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow0ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow0ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates (embed i) c) (childOrbitWords (embed i) c)
    (child_basis_eq i c)

end JoinChunk64

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ModuleRegistry

end
