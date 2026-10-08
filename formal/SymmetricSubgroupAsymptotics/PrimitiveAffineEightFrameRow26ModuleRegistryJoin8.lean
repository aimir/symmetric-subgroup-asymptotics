import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistryOldTableData8
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistryOrbitTableData8

/-! Selected invariant-state cyclic joins 8–14. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistry

local instance sourceGroupJoin8 : Group Source := PrimitiveAffineEightFrameTop17TopCertificate.group
local instance sourceInhabitedJoin8 : Inhabited Source := ⟨1⟩

namespace JoinChunk8

def embed (i : Fin 7) : Fin 15 :=
  ⟨8 + i.val, by omega⟩

private def childOldCoordinates (i : Fin 7)
    (c : Fin 15)
    (j : Fin (PrimitiveAffineEightFrameRow26ModuleRepresentation.charts (child (embed i) c)).1) :
    Fin (PrimitiveAffineEightFrameRow26ModuleRepresentation.charts (embed i)).1 → ZMod 2 :=
  binaryVectorOfMask (PrimitiveAffineEightFrameRow26ModuleRepresentation.charts (embed i)).1
    ((SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistryOldTableData8.childOldMasks i c)[j.val]!)

private def childOrbitWords (i : Fin 7)
    (c : Fin 15)
    (j : Fin (PrimitiveAffineEightFrameRow26ModuleRepresentation.charts (child (embed i) c)).1) : List Source :=
  (SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistryOrbitTableData8.childOrbitRows i c)[j.val]!

private theorem old_mem_child : ∀ i : Fin 7, ∀ c j,
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow26ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 7, ∀ c,
    PrimitiveAffineEightFrameRow26ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow26ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 7, ∀ c j,
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates i c j) +
        ((childOrbitWords i c j).map (fun g ↦
          PrimitiveAffineEightFrameRow26ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow26ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;>
    simp only [childOldCoordinates, childOrbitWords] <;>
    native_decide +revert

theorem child_eq (i : Fin 7) (c : Fin 15) :
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow26ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow26ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow26ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow26ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow26ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow26ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates i c) (childOrbitWords i c)
    (child_basis_eq i c)

end JoinChunk8

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow26ModuleRegistry

end
