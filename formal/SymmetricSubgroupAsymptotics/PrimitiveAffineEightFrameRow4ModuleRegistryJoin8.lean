import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleRegistryOldTableData8
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleRegistryOrbitTableData8

/-! Selected invariant-state cyclic joins 8–13. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleRegistry

local instance sourceGroupJoin8 : Group Source := PrimitiveAffineEightFrameRow4TopCertificate.group
local instance sourceInhabitedJoin8 : Inhabited Source := ⟨1⟩

namespace JoinChunk8

def embed (i : Fin 6) : Fin 14 :=
  ⟨8 + i.val, by omega⟩

private def childOldCoordinates (i : Fin 6)
    (c : Fin 14)
    (j : Fin (PrimitiveAffineEightFrameRow4ModuleRepresentation.charts (child (embed i) c)).1) :
    Fin (PrimitiveAffineEightFrameRow4ModuleRepresentation.charts (embed i)).1 → ZMod 2 :=
  binaryVectorOfMask (PrimitiveAffineEightFrameRow4ModuleRepresentation.charts (embed i)).1
    ((SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleRegistryOldTableData8.childOldMasks i c)[j.val]!)

private def childOrbitWords (i : Fin 6)
    (c : Fin 14)
    (j : Fin (PrimitiveAffineEightFrameRow4ModuleRepresentation.charts (child (embed i) c)).1) : List Source :=
  (SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleRegistryOrbitTableData8.childOrbitRows i c)[j.val]!

private theorem old_mem_child : ∀ i : Fin 6, ∀ c j,
    (PrimitiveAffineEightFrameRow4ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow4ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow4ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 6, ∀ c,
    PrimitiveAffineEightFrameRow4ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow4ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow4ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 6, ∀ c j,
    (PrimitiveAffineEightFrameRow4ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow4ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates i c j) +
        ((childOrbitWords i c j).map (fun g ↦
          PrimitiveAffineEightFrameRow4ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow4ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;>
    simp only [childOldCoordinates, childOrbitWords] <;>
    native_decide +revert

theorem child_eq (i : Fin 6) (c : Fin 14) :
    (PrimitiveAffineEightFrameRow4ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow4ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow4ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow4ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow4ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow4ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow4ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow4ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow4ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow4ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow4ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow4ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates i c) (childOrbitWords i c)
    (child_basis_eq i c)

end JoinChunk8

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4ModuleRegistry

end
