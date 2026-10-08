import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow10ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow10ModuleRegistryOldTableData0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow10ModuleRegistryOrbitTableData0

/-! Selected invariant-state cyclic joins 0–9. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow10ModuleRegistry

local instance sourceGroupJoin0 : Group Source := PrimitiveAffineEightFrameTop8TopCertificate.group
local instance sourceInhabitedJoin0 : Inhabited Source := ⟨1⟩

namespace JoinChunk0

def embed (i : Fin 10) : Fin 10 :=
  ⟨0 + i.val, by omega⟩

private def childOldCoordinates (i : Fin 10)
    (c : Fin 10)
    (j : Fin (PrimitiveAffineEightFrameRow10ModuleRepresentation.charts (child (embed i) c)).1) :
    Fin (PrimitiveAffineEightFrameRow10ModuleRepresentation.charts (embed i)).1 → ZMod 2 :=
  binaryVectorOfMask (PrimitiveAffineEightFrameRow10ModuleRepresentation.charts (embed i)).1
    ((SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow10ModuleRegistryOldTableData0.childOldMasks i c)[j.val]!)

private def childOrbitWords (i : Fin 10)
    (c : Fin 10)
    (j : Fin (PrimitiveAffineEightFrameRow10ModuleRepresentation.charts (child (embed i) c)).1) : List Source :=
  (SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow10ModuleRegistryOrbitTableData0.childOrbitRows i c)[j.val]!

private theorem old_mem_child : ∀ i : Fin 10, ∀ c j,
    (PrimitiveAffineEightFrameRow10ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow10ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow10ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 10, ∀ c,
    PrimitiveAffineEightFrameRow10ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow10ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow10ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 10, ∀ c j,
    (PrimitiveAffineEightFrameRow10ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow10ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates i c j) +
        ((childOrbitWords i c j).map (fun g ↦
          PrimitiveAffineEightFrameRow10ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow10ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;>
    simp only [childOldCoordinates, childOrbitWords] <;>
    native_decide +revert

theorem child_eq (i : Fin 10) (c : Fin 10) :
    (PrimitiveAffineEightFrameRow10ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow10ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow10ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow10ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow10ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow10ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow10ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow10ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow10ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow10ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow10ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow10ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates i c) (childOrbitWords i c)
    (child_basis_eq i c)

end JoinChunk0

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow10ModuleRegistry

end
