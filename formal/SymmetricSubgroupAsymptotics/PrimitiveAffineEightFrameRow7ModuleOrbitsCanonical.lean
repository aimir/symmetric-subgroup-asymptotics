import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleOrbitsData

/-! Selected row 7 canonical cyclic spans. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleOrbitsCanonical

abbrev Source := PrimitiveAffineEightFrameRow7ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow7TopCertificate.group

namespace C0

private def words (j : Fin 0) : List Source := []

private theorem representative_mem :
    PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 0 ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 0).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 0).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow7ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 0))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 0).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 0) := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 0).2
    PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 0)
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space 0)
    (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 0) representative_mem words basis_eq

end C0

namespace C1

private def words (j : Fin 4) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,6]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 1 ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 1).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 1).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow7ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 1))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 1).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 1) := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 1).2
    PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 1)
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space 1)
    (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 1) representative_mem words basis_eq

end C1

namespace C2

private def words (j : Fin 5) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord []] else (if j.val < 4 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 2 ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 2).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 2).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow7ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 2))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 2).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 2) := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 2).2
    PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 2)
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space 2)
    (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 2) representative_mem words basis_eq

end C2

namespace C3

private def words (j : Fin 5) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord []] else (if j.val < 4 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [5]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 3 ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 3).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 3).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow7ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 3))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 3).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 3) := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 3).2
    PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 3)
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space 3)
    (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 3) representative_mem words basis_eq

end C3

namespace C4

private def words (j : Fin 5) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord []] else (if j.val < 4 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [4]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [5]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 4 ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 4).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 4).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow7ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 4))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 4).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 4) := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 4).2
    PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 4)
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space 4)
    (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 4) representative_mem words basis_eq

end C4

namespace C5

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [2,6]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1,6]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 5 ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 5).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 5).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow7ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 5))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 5).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 5) := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 5).2
    PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 5)
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space 5)
    (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 5) representative_mem words basis_eq

end C5

namespace C6

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [2]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1,6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [2,6]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [2,6]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 6 ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 6).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 6).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow7ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 6))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 6).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 6) := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 6).2
    PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 6)
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space 6)
    (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 6) representative_mem words basis_eq

end C6

namespace C7

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [2]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1,6]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1,6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [2,6]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 7 ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 7).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 7).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow7ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 7))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 7).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 7) := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 7).2
    PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 7)
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space 7)
    (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 7) representative_mem words basis_eq

end C7

namespace C8

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord []] else (if j.val < 5 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [5]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 8 ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 9).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 9).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow7ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 8))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 9).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 8) := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 9).2
    PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 9)
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space 9)
    (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 8) representative_mem words basis_eq

end C8

namespace C9

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [2]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord []])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 9 ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 10).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 10).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow7ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 9))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 10).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 9) := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 10).2
    PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 10)
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space 10)
    (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 9) representative_mem words basis_eq

end C9

namespace C10

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord []])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 10 ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 11).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 11).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow7ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 10))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 11).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 10) := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 11).2
    PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 11)
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space 11)
    (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 10) representative_mem words basis_eq

end C10

namespace C11

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [2]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,6]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [2,6]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1,6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [2,6]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 11 ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 16).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 16).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow7ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 11))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 16).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 11) := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 16).2
    PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 16)
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space 16)
    (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 11) representative_mem words basis_eq

end C11

namespace C12

private def words (j : Fin 9) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,2]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3,3]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3,3]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3,5]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 12 ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 17).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 17).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow7ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 12))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 17).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 12) := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 17).2
    PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 17)
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space 17)
    (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 12) representative_mem words basis_eq

end C12

namespace C13

private def words (j : Fin 9) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3,3]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3,3]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3,3],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3,5]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3,3]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 13 ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 18).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 18).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow7ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 13))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 18).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 13) := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 18).2
    PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 18)
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space 18)
    (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 13) representative_mem words basis_eq

end C13

namespace C14

private def words (j : Fin 9) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,2]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3,3]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3,5]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3,3],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3,5]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 14 ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 19).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 19).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow7ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 14))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 19).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 14) := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 19).2
    PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 19)
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space 19)
    (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 14) representative_mem words basis_eq

end C14

namespace C15

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,2]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0,6]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,6]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1,6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0,6]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,2,6]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 15 ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 20).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 20).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow7ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 15))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 20).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 15) := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 20).2
    PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 20)
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space 20)
    (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 15) representative_mem words basis_eq

end C15

namespace C16

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0,6]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0,6]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1,6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0,6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,2,6]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1,6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0,6]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 16 ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 21).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 21).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow7ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 16))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 21).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 16) := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 21).2
    PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 21)
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space 21)
    (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 16) representative_mem words basis_eq

end C16

namespace C17

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,2]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,6]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0,6]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,2,6]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1,6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0,6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,2,6]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 17 ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 22).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 22).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow7ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 17))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 22).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 17) := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 22).2
    PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 22)
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space 22)
    (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 17) representative_mem words basis_eq

end C17

namespace C18

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,2]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,6]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,6]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1,6]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,6]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 18 ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 24).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 24).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow7ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 18))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 24).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 18) := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 24).2
    PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 24)
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space 24)
    (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 18) representative_mem words basis_eq

end C18

namespace C19

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,2]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord []]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,6]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,6]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1,6]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 19 ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 25).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 25).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow7ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 19))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 25).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 19) := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 25).2
    PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 25)
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space 25)
    (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 19) representative_mem words basis_eq

end C19

namespace C20

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,2]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord []]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,6]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,6]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1,6]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 20 ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 26).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 26).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow7ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 20))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 26).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 20) := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 26).2
    PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 26)
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space 26)
    (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 20) representative_mem words basis_eq

end C20

namespace C21

private def words (j : Fin 16) : List Source := (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,2]]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [6]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,1,6]]) else (if j.val < 11 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [2,6]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [2,6],PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,0,6]])) else (if j.val < 14 then (if j.val < 13 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1,6]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,6]]) else (if j.val < 15 then [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [1,2,6]] else [PrimitiveAffineEightFrameRow7ModuleOrbitsData.sourceWord [0,2,6]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 21 ∈
      (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 31).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 31).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow7ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 21))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 31).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 21) := by
  rw [PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.charts 31).2
    PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states 31)
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states_space 31)
    (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative 21) representative_mem words basis_eq

end C21

theorem canonical_span (i : Fin 22) :
    (PrimitiveAffineEightFrameRow7ModuleRepresentation.states (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicState i)).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow7ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow7ModuleOrbitsData.cyclicRepresentative i) := by
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
  · exact C14.span_eq
  · exact C15.span_eq
  · exact C16.span_eq
  · exact C17.span_eq
  · exact C18.span_eq
  · exact C19.span_eq
  · exact C20.span_eq
  · exact C21.span_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow7ModuleOrbitsCanonical

end
