import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleRegistryOldTableData0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleRegistryOrbitTableData0

/-! Selected invariant-state cyclic joins 0–10. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleRegistry

local instance sourceGroupJoin0 : Group Source := PrimitiveAffineEightFrameTop8TopCertificate.group
local instance sourceInhabitedJoin0 : Inhabited Source := ⟨1⟩

namespace JoinChunk0

def embed (i : Fin 11) : Fin 11 :=
  ⟨0 + i.val, by omega⟩

private def childOldCoordinates (i : Fin 11)
    (c : Fin 11)
    (j : Fin (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts (child (embed i) c)).1) :
    Fin (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts (embed i)).1 → ZMod 2 :=
  binaryVectorOfMask (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts (embed i)).1
    ((SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleRegistryOldTableData0.childOldMasks i c)[j.val]!)

private def childOrbitWords (i : Fin 11)
    (c : Fin 11)
    (j : Fin (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts (child (embed i) c)).1) : List Source :=
  (SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleRegistryOrbitTableData0.childOrbitRows i c)[j.val]!

private theorem old_mem_child : ∀ i : Fin 11, ∀ c j,
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow12ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 11, ∀ c,
    PrimitiveAffineEightFrameRow12ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow12ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 11, ∀ c j,
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates i c j) +
        ((childOrbitWords i c j).map (fun g ↦
          PrimitiveAffineEightFrameRow12ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow12ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;>
    simp only [childOldCoordinates, childOrbitWords] <;>
    native_decide +revert

theorem child_eq (i : Fin 11) (c : Fin 11) :
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow12ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow12ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow12ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates i c) (childOrbitWords i c)
    (child_basis_eq i c)

end JoinChunk0

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleRegistry

end
