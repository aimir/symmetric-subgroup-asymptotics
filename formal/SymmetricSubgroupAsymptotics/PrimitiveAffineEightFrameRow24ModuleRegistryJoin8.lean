import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistryJoinData
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistryOldTableData8
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistryOrbitTableData8

/-! Selected invariant-state cyclic joins 8–15. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistry

local instance sourceGroupJoin8 : Group Source := PrimitiveAffineEightFrameTop15TopCertificate.group
local instance sourceInhabitedJoin8 : Inhabited Source := ⟨1⟩

namespace JoinChunk8

def embed (i : Fin 8) : Fin 17 :=
  ⟨8 + i.val, by omega⟩

private def childOldCoordinates (i : Fin 8)
    (c : Fin 17)
    (j : Fin (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts (child (embed i) c)).1) :
    Fin (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts (embed i)).1 → ZMod 2 :=
  binaryVectorOfMask (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts (embed i)).1
    ((SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistryOldTableData8.childOldMasks i c)[j.val]!)

private def childOrbitWords (i : Fin 8)
    (c : Fin 17)
    (j : Fin (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts (child (embed i) c)).1) : List Source :=
  (SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistryOrbitTableData8.childOrbitRows i c)[j.val]!

private theorem old_mem_child : ∀ i : Fin 8, ∀ c j,
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ ((PrimitiveAffineEightFrameRow24ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin 8, ∀ c,
    PrimitiveAffineEightFrameRow24ModuleOrbits.cyclicRepresentative c ∈
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts (child (embed i) c)).2.space := by
  intro i c
  apply ((PrimitiveAffineEightFrameRow24ModuleRepresentation.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin 8, ∀ c j,
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts (embed i)).2.inclusion
          (childOldCoordinates i c j) +
        ((childOrbitWords i c j).map (fun g ↦
          PrimitiveAffineEightFrameRow24ModuleRepresentation.representation g
            (PrimitiveAffineEightFrameRow24ModuleOrbits.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;>
    simp only [childOldCoordinates, childOrbitWords] <;>
    native_decide +revert

theorem child_eq (i : Fin 8) (c : Fin 17) :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states (child (embed i) c)).toSubmodule =
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
          (PrimitiveAffineEightFrameRow24ModuleOrbits.cyclicRepresentative c) := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space,
    PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  exact binaryCoordinate_orbit_join_eq
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts (embed i)).2
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts (child (embed i) c)).2
    PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states (child (embed i) c))
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space (child (embed i) c))
    (PrimitiveAffineEightFrameRow24ModuleOrbits.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates i c) (childOrbitWords i c)
    (child_basis_eq i c)

end JoinChunk8

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleRegistry

end
