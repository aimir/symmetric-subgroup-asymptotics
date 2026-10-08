import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleRegistryOldTableData8
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleRegistryOrbitTableData8

/-! Selected invariant-state cyclic joins 8–11. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleRegistry

local instance sourceGroupJoin8 : Group Source := PrimitiveAffineEightFrameTop10TopCertificate.group
local instance sourceInhabitedJoin8 : Inhabited Source := ⟨1⟩

namespace JoinChunk8

def embed (i : Fin 4) : Fin 12 :=
  ⟨8 + i.val, by omega⟩

private def childOldCoordinates (i : Fin 4)
    (c : Fin 12)
    (j : Fin (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts (child (embed i) c)).1) :
    Fin (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts (embed i)).1 → ZMod 2 :=
  binaryVectorOfMask (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts (embed i)).1
    ((SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleRegistryOldTableData8.childOldMasks i c)[j.val]!)

private def childOrbitWords (i : Fin 4)
    (c : Fin 12)
    (j : Fin (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts (child (embed i) c)).1) : List Source :=
  (SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleRegistryOrbitTableData8.childOrbitRows i c)[j.val]!

private theorem old_mem_child : ∀ i : Fin 4, ∀ c j,
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow19ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 4, ∀ c,
    PrimitiveAffineEightFrameRow19ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow19ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 4, ∀ c j,
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates i c j) +
        ((childOrbitWords i c j).map (fun g ↦
          PrimitiveAffineEightFrameRow19ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow19ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;>
    simp only [childOldCoordinates, childOrbitWords] <;>
    native_decide +revert

theorem child_eq (i : Fin 4) (c : Fin 12) :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow19ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow19ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates i c) (childOrbitWords i c)
    (child_basis_eq i c)

end JoinChunk8

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleRegistry

end
