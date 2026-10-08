import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow13ModuleOrbitsData

/-! Selected row 13 canonical cyclic spans. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow13ModuleOrbitsCanonical

abbrev Source := PrimitiveAffineEightFrameRow13ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop8TopCertificate.group

namespace C0

private def words (j : Fin 0) : List Source := []

private theorem representative_mem :
    PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 0 ∈
      (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 0).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 0).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow13ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 0))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 0).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 0) := by
  rw [PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 0).2
    PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 0)
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space 0)
    (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 0) representative_mem words basis_eq

end C0

namespace C1

private def words (j : Fin 4) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [7]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,7]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 1 ∈
      (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 1).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 1).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow13ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 1))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 1).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 1) := by
  rw [PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 1).2
    PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 1)
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space 1)
    (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 1) representative_mem words basis_eq

end C1

namespace C2

private def words (j : Fin 5) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord []] else (if j.val < 4 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [6]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [5]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 2 ∈
      (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 2).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 2).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow13ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 2))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 2).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 2) := by
  rw [PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 2).2
    PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 2)
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space 2)
    (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 2) representative_mem words basis_eq

end C2

namespace C3

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [2]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [7]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [2,7],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [3,7]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [2,7]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 3 ∈
      (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 3).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 3).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow13ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 3))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 3).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 3) := by
  rw [PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 3).2
    PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 3)
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space 3)
    (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 3) representative_mem words basis_eq

end C3

namespace C4

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [3]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord []])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [6]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [6]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 4 ∈
      (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 4).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 4).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow13ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 4))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 4).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 4) := by
  rw [PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 4).2
    PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 4)
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space 4)
    (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 4) representative_mem words basis_eq

end C4

namespace C5

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [2]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord []])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [6]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [6]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 5 ∈
      (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 5).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 5).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow13ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 5))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 5).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 5) := by
  rw [PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 5).2
    PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 5)
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space 5)
    (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 5) representative_mem words basis_eq

end C5

namespace C6

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [2]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [7]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,7]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [3,7]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [7],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,7],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [2,7]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 6 ∈
      (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 7).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 7).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow13ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 6))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 7).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 6) := by
  rw [PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 7).2
    PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 7)
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space 7)
    (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 6) representative_mem words basis_eq

end C6

namespace C7

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [3]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [7]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,7]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [3,7]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,7],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [2,7],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [3,7]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 7 ∈
      (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 8).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 8).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow13ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 7))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 8).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 7) := by
  rw [PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 8).2
    PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 8)
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space 8)
    (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 7) representative_mem words basis_eq

end C7

namespace C8

private def words (j : Fin 9) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1,0]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1,3]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [4,0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [4]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [4,0],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [4,6]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [4,6]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 8 ∈
      (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 9).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 9).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow13ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 8))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 9).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 8) := by
  rw [PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 9).2
    PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 9)
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space 9)
    (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 8) representative_mem words basis_eq

end C8

namespace C9

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1,3]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [7]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1,0,7]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1,7]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [7],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1,7],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [2,7],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1,0,7],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1,3,7]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [7],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1,3,7]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 9 ∈
      (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 10).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 10).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow13ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 9))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 10).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 9) := by
  rw [PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 10).2
    PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 10)
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space 10)
    (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 9) representative_mem words basis_eq

end C9

namespace C10

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,1]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord []]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,4]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,4]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,5]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 10 ∈
      (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 11).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 11).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow13ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 10))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 11).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 10) := by
  rw [PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 11).2
    PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 11)
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space 11)
    (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 10) representative_mem words basis_eq

end C10

namespace C11

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,2]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord []]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,4]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,4]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,5]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 11 ∈
      (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 12).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 12).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow13ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 11))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 12).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 11) := by
  rw [PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 12).2
    PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 12)
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space 12)
    (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 11) representative_mem words basis_eq

end C11

namespace C12

private def words (j : Fin 12) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,1]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,1]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,2]]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [7]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,7]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,1,7]])) else (if j.val < 10 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1,7],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,1,7]] else (if j.val < 11 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [2,7],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,1,7]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1,7],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,1,7],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,2,7]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 12 ∈
      (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 14).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 14).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow13ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 12))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 14).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 12) := by
  rw [PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 14).2
    PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 14)
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space 14)
    (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 12) representative_mem words basis_eq

end C12

namespace C13

private def words (j : Fin 16) : List Source := (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,3]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [2]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,2]]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [7]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,3,7]]) else (if j.val < 11 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [3,7]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,7]])) else (if j.val < 14 then (if j.val < 13 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [2,7]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1,7],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [2,7]]) else (if j.val < 15 then [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,2,7],PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [1,3,7]] else [PrimitiveAffineEightFrameRow13ModuleOrbitsData.sourceWord [0,2,7]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 13 ∈
      (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 15).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 15).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow13ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 13))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 15).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 13) := by
  rw [PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.charts 15).2
    PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states 15)
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states_space 15)
    (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative 13) representative_mem words basis_eq

end C13

theorem canonical_span (i : Fin 14) :
    (PrimitiveAffineEightFrameRow13ModuleRepresentation.states (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicState i)).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow13ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow13ModuleOrbitsData.cyclicRepresentative i) := by
  fin_cases i
  · exact C0.span_eq
  · exact C1.span_eq
  · exact C2.span_eq
  · exact C3.span_eq
  · exact C4.span_eq
  · exact C5.span_eq
  · exact C6.span_eq
  · exact C7.span_eq
  · exact C8.span_eq
  · exact C9.span_eq
  · exact C10.span_eq
  · exact C11.span_eq
  · exact C12.span_eq
  · exact C13.span_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow13ModuleOrbitsCanonical

end
