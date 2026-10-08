import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleOrbitsData

/-! Selected row 16 canonical cyclic spans. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleOrbitsCanonical

abbrev Source := PrimitiveAffineEightFrameRow16ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop9TopCertificate.group

namespace C0

private def words (j : Fin 0) : List Source := []

private theorem representative_mem :
    PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 0 ∈
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 0).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 0).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow16ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 0))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 0).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow16ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 0) := by
  rw [PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 0).2
    PrimitiveAffineEightFrameRow16ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 0)
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space 0)
    (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 0) representative_mem words basis_eq

end C0

namespace C1

private def words (j : Fin 4) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [7]] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0,7]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 1 ∈
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 1).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 1).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow16ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 1))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 1).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow16ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 1) := by
  rw [PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 1).2
    PrimitiveAffineEightFrameRow16ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 1)
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space 1)
    (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 1) representative_mem words basis_eq

end C1

namespace C2

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [2]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [7]] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0,7]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [3,7]] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [7],PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0,7],PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [2,7]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 2 ∈
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 2).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 2).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow16ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 2))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 2).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow16ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 2) := by
  rw [PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 2).2
    PrimitiveAffineEightFrameRow16ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 2)
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space 2)
    (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 2) representative_mem words basis_eq

end C2

namespace C3

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [3]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [7]] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0,7]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [3,7]] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0,7],PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [2,7],PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [3,7]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 3 ∈
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 3).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 3).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow16ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 3))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 3).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow16ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 3) := by
  rw [PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 3).2
    PrimitiveAffineEightFrameRow16ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 3)
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space 3)
    (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 3) representative_mem words basis_eq

end C3

namespace C4

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [2,4]] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [2,4]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [4]] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [7]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [7],PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0,5]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 4 ∈
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 4).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 4).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow16ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 4))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 4).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow16ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 4) := by
  rw [PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 4).2
    PrimitiveAffineEightFrameRow16ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 4)
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space 4)
    (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 4) representative_mem words basis_eq

end C4

namespace C5

private def words (j : Fin 12) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [1]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0,1]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0,2]]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [7]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0,7]] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [1,7]])) else (if j.val < 10 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0,1,7]] else (if j.val < 11 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [1,7],PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [2,7]] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0,1,7],PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0,2,7]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 5 ∈
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 5).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 5).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow16ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 5))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 5).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow16ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 5) := by
  rw [PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 5).2
    PrimitiveAffineEightFrameRow16ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 5)
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space 5)
    (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 5) representative_mem words basis_eq

end C5

namespace C6

private def words (j : Fin 16) : List Source := (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [4]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [1,0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0,2]]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [7]] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [4,7]]) else (if j.val < 11 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [3,7]] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0,7]])) else (if j.val < 14 then (if j.val < 13 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [1,7]] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [1,0,7]]) else (if j.val < 15 then [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [1,3,7]] else [PrimitiveAffineEightFrameRow16ModuleOrbitsData.sourceWord [0,2,7]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 6 ∈
      (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 6).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 6).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow16ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 6))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 6).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow16ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 6) := by
  rw [PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.charts 6).2
    PrimitiveAffineEightFrameRow16ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states 6)
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states_space 6)
    (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative 6) representative_mem words basis_eq

end C6

theorem canonical_span (i : Fin 7) :
    (PrimitiveAffineEightFrameRow16ModuleRepresentation.states (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicState i)).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow16ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow16ModuleOrbitsData.cyclicRepresentative i) := by
  fin_cases i
  · exact C0.span_eq
  · exact C1.span_eq
  · exact C2.span_eq
  · exact C3.span_eq
  · exact C4.span_eq
  · exact C5.span_eq
  · exact C6.span_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow16ModuleOrbitsCanonical

end
