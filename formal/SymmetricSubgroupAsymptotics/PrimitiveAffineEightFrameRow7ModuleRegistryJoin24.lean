import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleRegistryOldTableData24
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleRegistryOrbitTableData24

/-! Selected invariant-state cyclic joins 24–31. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleRegistry

local instance sourceGroupJoin24 : Group Source := PrimitiveAffineEightFrameRow7TopCertificate.group
local instance sourceInhabitedJoin24 : Inhabited Source := ⟨1⟩

namespace JoinChunk24

def embed (i : Fin 8) : Fin 32 :=
  ⟨24 + i.val, by omega⟩

private def childOldCoordinates (i : Fin 8)
    (c : Fin 22)
    (j : Fin (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts (child (embed i) c)).1) :
    Fin (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts (embed i)).1 → ZMod 2 :=
  binaryVectorOfMask (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts (embed i)).1
    ((SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleRegistryOldTableData24.childOldMasks i c)[j.val]!)

private def childOrbitWords (i : Fin 8)
    (c : Fin 22)
    (j : Fin (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts (child (embed i) c)).1) : List Source :=
  (SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleRegistryOrbitTableData24.childOrbitRows i c)[j.val]!

private theorem old_mem_child : ∀ i : Fin 8, ∀ c j,
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow7ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 8, ∀ c,
    PrimitiveAffineEightFrameRow7ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow7ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 8, ∀ c j,
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates i c j) +
        ((childOrbitWords i c j).map (fun g ↦
          PrimitiveAffineEightFrameRow7ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow7ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;>
    simp only [childOldCoordinates, childOrbitWords] <;>
    native_decide +revert

theorem child_eq (i : Fin 8) (c : Fin 22) :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow7ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow7ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates i c) (childOrbitWords i c)
    (child_basis_eq i c)

end JoinChunk24

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleRegistry

end
