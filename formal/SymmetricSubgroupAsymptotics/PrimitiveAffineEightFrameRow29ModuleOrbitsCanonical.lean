import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29ModuleOrbitsData

/-! Selected row 29 canonical cyclic spans. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29ModuleOrbitsCanonical

abbrev Source := PrimitiveAffineEightFrameRow29ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow29TopCertificate.group

namespace C0

private def words (j : Fin 0) : List Source := []

private theorem representative_mem :
    PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicRepresentative 0 ∈
      (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts 0).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts 0).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow29ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicRepresentative 0))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states 0).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow29ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicRepresentative 0) := by
  rw [PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts 0).2
    PrimitiveAffineEightFrameRow29ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states 0)
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space 0)
    (PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicRepresentative 0) representative_mem words basis_eq

end C0

namespace C1

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1,0,2]] else [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1,0,2],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,1,0,2]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1,0]] else [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,1,0]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicRepresentative 1 ∈
      (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts 1).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts 1).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow29ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicRepresentative 1))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states 1).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow29ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicRepresentative 1) := by
  rw [PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts 1).2
    PrimitiveAffineEightFrameRow29ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states 1)
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space 1)
    (PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicRepresentative 1) representative_mem words basis_eq

end C1

namespace C2

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,1,0,2]] else [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1,0,2]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,1,0]] else [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1,0]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicRepresentative 2 ∈
      (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts 2).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts 2).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow29ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicRepresentative 2))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states 2).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow29ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicRepresentative 2) := by
  rw [PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts 2).2
    PrimitiveAffineEightFrameRow29ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states 2)
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space 2)
    (PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicRepresentative 2) representative_mem words basis_eq

end C2

namespace C3

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1,0,2],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,1,0,2]] else [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,1,0,2]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,1,0]] else [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,1,0]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicRepresentative 3 ∈
      (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts 3).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts 3).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow29ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicRepresentative 3))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states 3).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow29ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicRepresentative 3) := by
  rw [PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts 3).2
    PrimitiveAffineEightFrameRow29ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states 3)
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space 3)
    (PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicRepresentative 3) representative_mem words basis_eq

end C3

namespace C4

private def words (j : Fin 16) : List Source := (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,0,2]] else [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,0,2]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,1,1]] else [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,0,1]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1,0,1]]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 11 then [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1,1,0,2]] else [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1,1,0,2],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,0,0,0,2]])) else (if j.val < 14 then (if j.val < 13 then [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1,1]] else [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1,1],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,0,0]]) else (if j.val < 15 then [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1,1,0]] else [PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [1,1,0],PrimitiveAffineEightFrameRow29ModuleOrbitsData.sourceWord [0,0,0,0]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicRepresentative 4 ∈
      (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts 4).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts 4).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow29ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicRepresentative 4))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states 4).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow29ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicRepresentative 4) := by
  rw [PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.charts 4).2
    PrimitiveAffineEightFrameRow29ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states 4)
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states_space 4)
    (PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicRepresentative 4) representative_mem words basis_eq

end C4

theorem canonical_span (i : Fin 5) :
    (PrimitiveAffineEightFrameRow29ModuleRepresentation.states (PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicState i)).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow29ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow29ModuleOrbitsData.cyclicRepresentative i) := by
  fin_cases i
  · exact C0.span_eq
  · exact C1.span_eq
  · exact C2.span_eq
  · exact C3.span_eq
  · exact C4.span_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29ModuleOrbitsCanonical

end
