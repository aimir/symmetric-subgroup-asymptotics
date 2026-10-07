import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistryOldTableData16
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistryOrbitTableData16

/-! Selected invariant-state cyclic joins 16–16. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistry

local instance sourceGroupJoin16 : Group Source := PrimitiveAffineEightFrameRow6TopCertificate.group
local instance sourceInhabitedJoin16 : Inhabited Source := ⟨1⟩

namespace JoinChunk16

def embed (i : Fin 1) : Fin 17 :=
  ⟨16 + i.val, by omega⟩

private def childOldCoordinates (i : Fin 1)
    (c : Fin 17)
    (j : Fin (PrimitiveAffineEightFrameRow6ModuleRepresentation.charts (child (embed i) c)).1) :
    Fin (PrimitiveAffineEightFrameRow6ModuleRepresentation.charts (embed i)).1 → ZMod 2 :=
  binaryVectorOfMask (PrimitiveAffineEightFrameRow6ModuleRepresentation.charts (embed i)).1
    ((SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistryOldTableData16.childOldMasks i c)[j.val]!)

private def childOrbitWords (i : Fin 1)
    (c : Fin 17)
    (j : Fin (PrimitiveAffineEightFrameRow6ModuleRepresentation.charts (child (embed i) c)).1) : List Source :=
  (SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistryOrbitTableData16.childOrbitRows i c)[j.val]!

private theorem old_mem_child : ∀ i : Fin 1, ∀ c j,
    (PrimitiveAffineEightFrameRow6ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow6ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow6ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 1, ∀ c,
    PrimitiveAffineEightFrameRow6ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow6ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow6ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 1, ∀ c j,
    (PrimitiveAffineEightFrameRow6ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow6ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates i c j) +
        ((childOrbitWords i c j).map (fun g ↦
          PrimitiveAffineEightFrameRow6ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow6ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;>
    simp only [childOldCoordinates, childOrbitWords] <;>
    native_decide +revert

theorem child_eq (i : Fin 1) (c : Fin 17) :
    (PrimitiveAffineEightFrameRow6ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow6ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow6ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow6ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow6ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow6ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow6ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow6ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow6ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow6ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow6ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow6ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates i c) (childOrbitWords i c)
    (child_basis_eq i c)

end JoinChunk16

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow6ModuleRegistry

end
