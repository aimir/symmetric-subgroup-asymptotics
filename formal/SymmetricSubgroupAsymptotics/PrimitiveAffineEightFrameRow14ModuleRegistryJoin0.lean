import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow14ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow14ModuleRegistryOldTableData0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow14ModuleRegistryOrbitTableData0

/-! Selected invariant-state cyclic joins 0–5. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow14ModuleRegistry

local instance sourceGroupJoin0 : Group Source := PrimitiveAffineEightFrameTop9TopCertificate.group
local instance sourceInhabitedJoin0 : Inhabited Source := ⟨1⟩

namespace JoinChunk0

def embed (i : Fin 6) : Fin 6 :=
  ⟨0 + i.val, by omega⟩

private def childOldCoordinates (i : Fin 6)
    (c : Fin 6)
    (j : Fin (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts (child (embed i) c)).1) :
    Fin (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts (embed i)).1 → ZMod 2 :=
  binaryVectorOfMask (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts (embed i)).1
    ((SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow14ModuleRegistryOldTableData0.childOldMasks i c)[j.val]!)

private def childOrbitWords (i : Fin 6)
    (c : Fin 6)
    (j : Fin (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts (child (embed i) c)).1) : List Source :=
  (SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow14ModuleRegistryOrbitTableData0.childOrbitRows i c)[j.val]!

private theorem old_mem_child : ∀ i : Fin 6, ∀ c j,
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow14ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 6, ∀ c,
    PrimitiveAffineEightFrameRow14ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow14ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 6, ∀ c j,
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates i c j) +
        ((childOrbitWords i c j).map (fun g ↦
          PrimitiveAffineEightFrameRow14ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow14ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;>
    simp only [childOldCoordinates, childOrbitWords] <;>
    native_decide +revert

theorem child_eq (i : Fin 6) (c : Fin 6) :
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow14ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow14ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow14ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow14ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow14ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow14ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow14ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates i c) (childOrbitWords i c)
    (child_basis_eq i c)

end JoinChunk0

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow14ModuleRegistry

end
