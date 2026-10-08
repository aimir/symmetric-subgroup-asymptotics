import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow13ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow13ModuleRegistryOldTableData0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow13ModuleRegistryOrbitTableData0

/-! Selected invariant-state cyclic joins 0–15. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow13ModuleRegistry

local instance sourceGroupJoin0 : Group Source := PrimitiveAffineEightFrameTop8TopCertificate.group
local instance sourceInhabitedJoin0 : Inhabited Source := ⟨1⟩

namespace JoinChunk0

def embed (i : Fin 16) : Fin 16 :=
  ⟨0 + i.val, by omega⟩

private def childOldCoordinates (i : Fin 16)
    (c : Fin 14)
    (j : Fin (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts (child (embed i) c)).1) :
    Fin (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts (embed i)).1 → ZMod 2 :=
  binaryVectorOfMask (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts (embed i)).1
    ((SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow13ModuleRegistryOldTableData0.childOldMasks i c)[j.val]!)

private def childOrbitWords (i : Fin 16)
    (c : Fin 14)
    (j : Fin (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts (child (embed i) c)).1) : List Source :=
  (SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow13ModuleRegistryOrbitTableData0.childOrbitRows i c)[j.val]!

private theorem old_mem_child : ∀ i : Fin 16, ∀ c j,
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow13ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 16, ∀ c,
    PrimitiveAffineEightFrameRow13ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow13ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 16, ∀ c j,
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates i c j) +
        ((childOrbitWords i c j).map (fun g ↦
          PrimitiveAffineEightFrameRow13ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow13ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;>
    simp only [childOldCoordinates, childOrbitWords] <;>
    native_decide +revert

theorem child_eq (i : Fin 16) (c : Fin 14) :
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow13ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow13ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow13ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates i c) (childOrbitWords i c)
    (child_basis_eq i c)

end JoinChunk0

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow13ModuleRegistry

end
