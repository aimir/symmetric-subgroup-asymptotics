import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistryOldTableData0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistryOrbitTableData0

/-! Selected invariant-state cyclic joins 0–7. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistry

local instance sourceGroupJoin0 : Group Source := PrimitiveAffineEightFrameTop9TopCertificate.group
local instance sourceInhabitedJoin0 : Inhabited Source := ⟨1⟩

namespace JoinChunk0

def embed (i : Fin 8) : Fin 12 :=
  ⟨0 + i.val, by omega⟩

private def childOldCoordinates (i : Fin 8)
    (c : Fin 12)
    (j : Fin (PrimitiveAffineEightFrameRow17ModuleRepresentation.charts (child (embed i) c)).1) :
    Fin (PrimitiveAffineEightFrameRow17ModuleRepresentation.charts (embed i)).1 → ZMod 2 :=
  binaryVectorOfMask (PrimitiveAffineEightFrameRow17ModuleRepresentation.charts (embed i)).1
    ((SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistryOldTableData0.childOldMasks i c)[j.val]!)

private def childOrbitWords (i : Fin 8)
    (c : Fin 12)
    (j : Fin (PrimitiveAffineEightFrameRow17ModuleRepresentation.charts (child (embed i) c)).1) : List Source :=
  (SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistryOrbitTableData0.childOrbitRows i c)[j.val]!

private theorem old_mem_child : ∀ i : Fin 8, ∀ c j,
    (PrimitiveAffineEightFrameRow17ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow17ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 8, ∀ c,
    PrimitiveAffineEightFrameRow17ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow17ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 8, ∀ c j,
    (PrimitiveAffineEightFrameRow17ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates i c j) +
        ((childOrbitWords i c j).map (fun g ↦
          PrimitiveAffineEightFrameRow17ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow17ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;>
    simp only [childOldCoordinates, childOrbitWords] <;>
    native_decide +revert

theorem child_eq (i : Fin 8) (c : Fin 12) :
    (PrimitiveAffineEightFrameRow17ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow17ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow17ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow17ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow17ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow17ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow17ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow17ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow17ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow17ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates i c) (childOrbitWords i c)
    (child_basis_eq i c)

end JoinChunk0

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow17ModuleRegistry

end
