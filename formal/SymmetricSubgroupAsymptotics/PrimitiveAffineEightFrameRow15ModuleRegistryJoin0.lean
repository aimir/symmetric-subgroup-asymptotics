import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleRegistryOldTableData0
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleRegistryOrbitTableData0

/-! Selected invariant-state cyclic joins 0–5. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleRegistry

local instance sourceGroupJoin0 : Group Source := PrimitiveAffineEightFrameTop9TopCertificate.group
local instance sourceInhabitedJoin0 : Inhabited Source := ⟨1⟩

namespace JoinChunk0

def embed (i : Fin 6) : Fin 6 :=
  ⟨0 + i.val, by omega⟩

private def childOldCoordinates (i : Fin 6)
    (c : Fin 6)
    (j : Fin (PrimitiveAffineEightFrameRow15ModuleRepresentation.charts (child (embed i) c)).1) :
    Fin (PrimitiveAffineEightFrameRow15ModuleRepresentation.charts (embed i)).1 → ZMod 2 :=
  binaryVectorOfMask (PrimitiveAffineEightFrameRow15ModuleRepresentation.charts (embed i)).1
    ((SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleRegistryOldTableData0.childOldMasks i c)[j.val]!)

private def childOrbitWords (i : Fin 6)
    (c : Fin 6)
    (j : Fin (PrimitiveAffineEightFrameRow15ModuleRepresentation.charts (child (embed i) c)).1) : List Source :=
  (SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleRegistryOrbitTableData0.childOrbitRows i c)[j.val]!

private theorem old_mem_child : ∀ i : Fin 6, ∀ c j,
    (PrimitiveAffineEightFrameRow15ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow15ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow15ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 6, ∀ c,
    PrimitiveAffineEightFrameRow15ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow15ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow15ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 6, ∀ c j,
    (PrimitiveAffineEightFrameRow15ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow15ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates i c j) +
        ((childOrbitWords i c j).map (fun g ↦
          PrimitiveAffineEightFrameRow15ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow15ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;>
    simp only [childOldCoordinates, childOrbitWords] <;>
    native_decide +revert

theorem child_eq (i : Fin 6) (c : Fin 6) :
    (PrimitiveAffineEightFrameRow15ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow15ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow15ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow15ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow15ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow15ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow15ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow15ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow15ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow15ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow15ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow15ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates i c) (childOrbitWords i c)
    (child_basis_eq i c)

end JoinChunk0

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow15ModuleRegistry

end
