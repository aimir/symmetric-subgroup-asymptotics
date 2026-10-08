import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow25ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow25ModuleRegistryOldTableData0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow25ModuleRegistryOrbitTableData0

/-! Selected invariant-state cyclic joins 0–7. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow25ModuleRegistry

local instance sourceGroupJoin0 : Group Source := PrimitiveAffineEightFrameTop16TopCertificate.group
local instance sourceInhabitedJoin0 : Inhabited Source := ⟨1⟩

namespace JoinChunk0

def embed (i : Fin 8) : Fin 17 :=
  ⟨0 + i.val, by omega⟩

private def childOldCoordinates (i : Fin 8)
    (c : Fin 17)
    (j : Fin (PrimitiveAffineEightFrameRow25ModuleRepresentation.charts (child (embed i) c)).1) :
    Fin (PrimitiveAffineEightFrameRow25ModuleRepresentation.charts (embed i)).1 → ZMod 2 :=
  binaryVectorOfMask (PrimitiveAffineEightFrameRow25ModuleRepresentation.charts (embed i)).1
    ((SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow25ModuleRegistryOldTableData0.childOldMasks i c)[j.val]!)

private def childOrbitWords (i : Fin 8)
    (c : Fin 17)
    (j : Fin (PrimitiveAffineEightFrameRow25ModuleRepresentation.charts (child (embed i) c)).1) : List Source :=
  (SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow25ModuleRegistryOrbitTableData0.childOrbitRows i c)[j.val]!

private theorem old_mem_child : ∀ i : Fin 8, ∀ c j,
    (PrimitiveAffineEightFrameRow25ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow25ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow25ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 8, ∀ c,
    PrimitiveAffineEightFrameRow25ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow25ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow25ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 8, ∀ c j,
    (PrimitiveAffineEightFrameRow25ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow25ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates i c j) +
        ((childOrbitWords i c j).map (fun g ↦
          PrimitiveAffineEightFrameRow25ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow25ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;>
    simp only [childOldCoordinates, childOrbitWords] <;>
    native_decide +revert

theorem child_eq (i : Fin 8) (c : Fin 17) :
    (PrimitiveAffineEightFrameRow25ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow25ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow25ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow25ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow25ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow25ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow25ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow25ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow25ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow25ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow25ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow25ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates i c) (childOrbitWords i c)
    (child_basis_eq i c)

end JoinChunk0

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow25ModuleRegistry

end
