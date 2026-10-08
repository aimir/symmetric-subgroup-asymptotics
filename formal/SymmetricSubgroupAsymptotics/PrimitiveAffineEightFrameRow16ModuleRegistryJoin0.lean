import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleRegistryOldTableData0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleRegistryOrbitTableData0

/-! Selected invariant-state cyclic joins 0–6. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleRegistry

local instance sourceGroupJoin0 : Group Source := PrimitiveAffineEightFrameTop9TopCertificate.group
local instance sourceInhabitedJoin0 : Inhabited Source := ⟨1⟩

namespace JoinChunk0

def embed (i : Fin 7) : Fin 7 :=
  ⟨0 + i.val, by omega⟩

private def childOldCoordinates (i : Fin 7)
    (c : Fin 7)
    (j : Fin (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts (child (embed i) c)).1) :
    Fin (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts (embed i)).1 → ZMod 2 :=
  binaryVectorOfMask (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts (embed i)).1
    ((SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleRegistryOldTableData0.childOldMasks i c)[j.val]!)

private def childOrbitWords (i : Fin 7)
    (c : Fin 7)
    (j : Fin (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts (child (embed i) c)).1) : List Source :=
  (SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleRegistryOrbitTableData0.childOrbitRows i c)[j.val]!

private theorem old_mem_child : ∀ i : Fin 7, ∀ c j,
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow16ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 7, ∀ c,
    PrimitiveAffineEightFrameRow16ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow16ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 7, ∀ c j,
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates i c j) +
        ((childOrbitWords i c j).map (fun g ↦
          PrimitiveAffineEightFrameRow16ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow16ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;>
    simp only [childOldCoordinates, childOrbitWords] <;>
    native_decide +revert

theorem child_eq (i : Fin 7) (c : Fin 7) :
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow16ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow16ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow16ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow16ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates i c) (childOrbitWords i c)
    (child_basis_eq i c)

end JoinChunk0

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleRegistry

end
