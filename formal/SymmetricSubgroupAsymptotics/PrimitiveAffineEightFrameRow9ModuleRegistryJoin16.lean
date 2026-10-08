import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistryOldTableData16
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistryOrbitTableData16

/-! Selected invariant-state cyclic joins 16–23. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistry

local instance sourceGroupJoin16 : Group Source := PrimitiveAffineEightFrameRow9TopCertificate.group
local instance sourceInhabitedJoin16 : Inhabited Source := ⟨1⟩

namespace JoinChunk16

def embed (i : Fin 8) : Fin 25 :=
  ⟨16 + i.val, by omega⟩

private def childOldCoordinates (i : Fin 8)
    (c : Fin 22)
    (j : Fin (PrimitiveAffineEightFrameRow9ModuleRepresentation.charts (child (embed i) c)).1) :
    Fin (PrimitiveAffineEightFrameRow9ModuleRepresentation.charts (embed i)).1 → ZMod 2 :=
  binaryVectorOfMask (PrimitiveAffineEightFrameRow9ModuleRepresentation.charts (embed i)).1
    ((SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistryOldTableData16.childOldMasks i c)[j.val]!)

private def childOrbitWords (i : Fin 8)
    (c : Fin 22)
    (j : Fin (PrimitiveAffineEightFrameRow9ModuleRepresentation.charts (child (embed i) c)).1) : List Source :=
  (SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistryOrbitTableData16.childOrbitRows i c)[j.val]!

private theorem old_mem_child : ∀ i : Fin 8, ∀ c j,
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow9ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 8, ∀ c,
    PrimitiveAffineEightFrameRow9ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow9ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 8, ∀ c j,
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates i c j) +
        ((childOrbitWords i c j).map (fun g ↦
          PrimitiveAffineEightFrameRow9ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow9ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;>
    simp only [childOldCoordinates, childOrbitWords] <;>
    native_decide +revert

theorem child_eq (i : Fin 8) (c : Fin 22) :
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow9ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow9ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow9ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow9ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow9ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow9ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates i c) (childOrbitWords i c)
    (child_basis_eq i c)

end JoinChunk16

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistry

end
