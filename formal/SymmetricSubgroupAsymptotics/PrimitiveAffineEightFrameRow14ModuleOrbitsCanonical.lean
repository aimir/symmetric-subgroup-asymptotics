import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow14ModuleOrbitsData

/-! Selected row 14 canonical cyclic spans. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow14ModuleOrbitsCanonical

abbrev Source := PrimitiveAffineEightFrameRow14ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop9TopCertificate.group

namespace C0

private def words (j : Fin 0) : List Source := []

private theorem representative_mem :
    PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative 0 ∈
      (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts 0).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts 0).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow14ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative 0))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.states 0).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow14ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative 0) := by
  rw [PrimitiveAffineEightFrameRow14ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts 0).2
    PrimitiveAffineEightFrameRow14ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.states 0)
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.states_space 0)
    (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative 0) representative_mem words basis_eq

end C0

namespace C1

private def words (j : Fin 4) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [7]] else [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0,7]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative 1 ∈
      (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts 1).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts 1).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow14ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative 1))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.states 1).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow14ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative 1) := by
  rw [PrimitiveAffineEightFrameRow14ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts 1).2
    PrimitiveAffineEightFrameRow14ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.states 1)
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.states_space 1)
    (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative 1) representative_mem words basis_eq

end C1

namespace C2

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [2]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [7]] else [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0,7]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [3,7]] else [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [7],PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0,7],PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [2,7]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative 2 ∈
      (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts 2).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts 2).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow14ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative 2))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.states 2).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow14ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative 2) := by
  rw [PrimitiveAffineEightFrameRow14ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts 2).2
    PrimitiveAffineEightFrameRow14ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.states 2)
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.states_space 2)
    (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative 2) representative_mem words basis_eq

end C2

namespace C3

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [3]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [7]] else [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0,7]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [3,7]] else [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0,7],PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [2,7],PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [3,7]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative 3 ∈
      (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts 3).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts 3).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow14ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative 3))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.states 3).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow14ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative 3) := by
  rw [PrimitiveAffineEightFrameRow14ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts 3).2
    PrimitiveAffineEightFrameRow14ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.states 3)
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.states_space 3)
    (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative 3) representative_mem words basis_eq

end C3

namespace C4

private def words (j : Fin 12) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0,1]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0,1]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0,2]]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [7]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0,7]] else [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0,1,7]])) else (if j.val < 10 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [1,7],PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0,1,7]] else (if j.val < 11 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [2,7],PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0,1,7]] else [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [1,7],PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0,1,7],PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0,2,7]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative 4 ∈
      (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts 4).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts 4).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow14ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative 4))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.states 4).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow14ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative 4) := by
  rw [PrimitiveAffineEightFrameRow14ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts 4).2
    PrimitiveAffineEightFrameRow14ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.states 4)
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.states_space 4)
    (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative 4) representative_mem words basis_eq

end C4

namespace C5

private def words (j : Fin 16) : List Source := (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [4]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [2]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0,2]]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [7]] else [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [4,7]]) else (if j.val < 11 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [3,7]] else [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0,7]])) else (if j.val < 14 then (if j.val < 13 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [2,7]] else [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [1,7],PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [2,7]]) else (if j.val < 15 then [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0,2,7],PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [1,3,7]] else [PrimitiveAffineEightFrameRow14ModuleOrbitsData.sourceWord [0,2,7]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative 5 ∈
      (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts 5).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts 5).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow14ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative 5))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.states 5).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow14ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative 5) := by
  rw [PrimitiveAffineEightFrameRow14ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.charts 5).2
    PrimitiveAffineEightFrameRow14ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.states 5)
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.states_space 5)
    (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative 5) representative_mem words basis_eq

end C5

theorem canonical_span (i : Fin 6) :
    (PrimitiveAffineEightFrameRow14ModuleRepresentation.states (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicState i)).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow14ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow14ModuleOrbitsData.cyclicRepresentative i) := by
  fin_cases i
  · exact C0.span_eq
  · exact C1.span_eq
  · exact C2.span_eq
  · exact C3.span_eq
  · exact C4.span_eq
  · exact C5.span_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow14ModuleOrbitsCanonical

end
