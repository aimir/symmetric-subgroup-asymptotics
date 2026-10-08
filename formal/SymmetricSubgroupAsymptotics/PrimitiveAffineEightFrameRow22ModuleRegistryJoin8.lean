import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistryOldTableData8
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistryOrbitTableData8

/-! Selected invariant-state cyclic joins 8–15. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistry

local instance sourceGroupJoin8 : Group Source := PrimitiveAffineEightFrameTop13TopCertificate.group
local instance sourceInhabitedJoin8 : Inhabited Source := ⟨1⟩

namespace JoinChunk8

def embed (i : Fin 8) : Fin 23 :=
  ⟨8 + i.val, by omega⟩

private def childOldCoordinates (i : Fin 8)
    (c : Fin 19)
    (j : Fin (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts (child (embed i) c)).1) :
    Fin (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts (embed i)).1 → ZMod 2 :=
  binaryVectorOfMask (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts (embed i)).1
    ((SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistryOldTableData8.childOldMasks i c)[j.val]!)

private def childOrbitWords (i : Fin 8)
    (c : Fin 19)
    (j : Fin (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts (child (embed i) c)).1) : List Source :=
  (SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistryOrbitTableData8.childOrbitRows i c)[j.val]!

private theorem old_mem_child : ∀ i : Fin 8, ∀ c j,
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow22ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 8, ∀ c,
    PrimitiveAffineEightFrameRow22ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow22ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 8, ∀ c j,
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates i c j) +
        ((childOrbitWords i c j).map (fun g ↦
          PrimitiveAffineEightFrameRow22ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow22ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;>
    simp only [childOldCoordinates, childOrbitWords] <;>
    native_decide +revert

theorem child_eq (i : Fin 8) (c : Fin 19) :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow22ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow22ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates i c) (childOrbitWords i c)
    (child_basis_eq i c)

end JoinChunk8

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleRegistry

end
