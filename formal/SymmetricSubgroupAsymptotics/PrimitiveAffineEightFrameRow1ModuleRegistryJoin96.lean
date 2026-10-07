import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryOldTableData96
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryOrbitTableData96

/-! Selected invariant-state cyclic joins 96–103. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistry

local instance sourceGroupJoin96 : Group Source := PrimitiveAffineEightFrameRow1TopCertificate.group
local instance sourceInhabitedJoin96 : Inhabited Source := ⟨1⟩

namespace JoinChunk96

def embed (i : Fin 8) : Fin 143 :=
  ⟨96 + i.val, by omega⟩

private def childOldCoordinates (i : Fin 8)
    (c : Fin 118)
    (j : Fin (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts (child (embed i) c)).1) :
    Fin (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts (embed i)).1 → ZMod 2 :=
  binaryVectorOfMask (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts (embed i)).1
    ((SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryOldTableData96.childOldMasks i c)[j.val]!)

private def childOrbitWords (i : Fin 8)
    (c : Fin 118)
    (j : Fin (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts (child (embed i) c)).1) : List Source :=
  (SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistryOrbitTableData96.childOrbitRows i c)[j.val]!

private theorem old_mem_child : ∀ i : Fin 8, ∀ c j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 8, ∀ c,
    PrimitiveAffineEightFrameRow1ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow1ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 8, ∀ c j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates i c j) +
        ((childOrbitWords i c j).map (fun g ↦
          PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow1ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;>
    simp only [childOldCoordinates, childOrbitWords] <;>
    native_decide +revert

theorem child_eq (i : Fin 8) (c : Fin 118) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow1ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow1ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates i c) (childOrbitWords i c)
    (child_basis_eq i c)

end JoinChunk96

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleRegistry

end
