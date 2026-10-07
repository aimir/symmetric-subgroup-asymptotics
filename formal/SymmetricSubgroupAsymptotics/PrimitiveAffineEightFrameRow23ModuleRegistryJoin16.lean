import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23ModuleRegistryJoinData

/-! Selected invariant-state cyclic joins 16–26. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23ModuleRegistry

local instance sourceGroupJoin16 : Group Source := PrimitiveAffineEightFrameRow23TopCertificate.group
local instance sourceInhabitedJoin16 : Inhabited Source := ⟨1⟩

namespace JoinChunk16

def embed (i : Fin 11) : Fin 27 :=
  ⟨16 + i.val, by omega⟩

private theorem old_mem_child : ∀ i : Fin 11, ∀ c j,
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 11, ∀ c,
    PrimitiveAffineEightFrameRow23ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow23ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 11, ∀ c j,
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates (embed i) c j) +
        ((childOrbitWords (embed i) c j).map (fun g ↦
          PrimitiveAffineEightFrameRow23ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow23ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;> native_decide +revert

theorem child_eq (i : Fin 11) (c : Fin 27) :
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow23ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow23ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow23ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow23ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow23ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow23ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates (embed i) c) (childOrbitWords (embed i) c)
    (child_basis_eq i c)

end JoinChunk16

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23ModuleRegistry

end
