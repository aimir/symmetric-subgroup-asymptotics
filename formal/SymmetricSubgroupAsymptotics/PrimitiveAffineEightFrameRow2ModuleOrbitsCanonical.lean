import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleOrbitsData

/-! Selected row 2 canonical cyclic spans. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleOrbitsCanonical

abbrev Source := PrimitiveAffineEightFrameRow2ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow2TopCertificate.group

namespace C0

private def words (j : Fin 0) : List Source := []

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 0 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 0).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 0).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 0))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 0).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 0) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 0).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 0)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 0)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 0) representative_mem words basis_eq

end C0

namespace C1

private def words (j : Fin 2) : List Source := (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0]])

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 1 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 1).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 1).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 1))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 1).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 1) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 1).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 1)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 1)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 1) representative_mem words basis_eq

end C1

namespace C2

private def words (j : Fin 4) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 2 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 2).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 2).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 2))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 2).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 2) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 2).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 2)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 2)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 2) representative_mem words basis_eq

end C2

namespace C3

private def words (j : Fin 5) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []] else (if j.val < 4 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [4]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 3 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 3).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 3).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 3))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 3).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 3) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 3).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 3)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 3)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 3) representative_mem words basis_eq

end C3

namespace C4

private def words (j : Fin 5) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []] else (if j.val < 4 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [4]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 4 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 4).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 4).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 4))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 4).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 4) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 4).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 4)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 4)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 4) representative_mem words basis_eq

end C4

namespace C5

private def words (j : Fin 5) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []] else (if j.val < 4 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 5 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 5).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 5).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 5))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 5).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 5) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 5).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 5)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 5)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 5) representative_mem words basis_eq

end C5

namespace C6

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1,5]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 6 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 6).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 6).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 6))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 6).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 6) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 6).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 6)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 6)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 6) representative_mem words basis_eq

end C6

namespace C7

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2,5]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 7 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 7).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 7).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 7))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 7).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 7) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 7).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 7)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 7)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 7) representative_mem words basis_eq

end C7

namespace C8

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2,5]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 8 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 8).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 8).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 8))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 8).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 8) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 8).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 8)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 8)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 8) representative_mem words basis_eq

end C8

namespace C9

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []] else (if j.val < 5 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 9 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 10).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 10).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 9))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 10).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 9) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 10).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 10)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 10)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 9) representative_mem words basis_eq

end C9

namespace C10

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [4]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 10 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 11).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 11).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 10))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 11).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 10) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 11).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 11)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 11)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 10) representative_mem words basis_eq

end C10

namespace C11

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [4]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 11 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 12).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 12).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 11))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 12).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 11) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 12).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 12)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 12)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 11) representative_mem words basis_eq

end C11

namespace C12

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [4]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 12 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 13).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 13).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 12))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 13).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 12) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 13).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 13)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 13)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 12) representative_mem words basis_eq

end C12

namespace C13

private def words (j : Fin 7) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 13 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 17).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 17).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 13))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 17).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 13) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 17).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 17)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 17)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 13) representative_mem words basis_eq

end C13

namespace C14

private def words (j : Fin 7) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,2]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 14 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 18).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 18).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 14))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 18).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 14) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 18).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 18)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 18)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 14) representative_mem words basis_eq

end C14

namespace C15

private def words (j : Fin 7) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,2]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 15 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 19).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 19).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 15))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 19).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 15) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 19).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 19)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 19)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 15) representative_mem words basis_eq

end C15

namespace C16

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 16 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 21).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 21).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 16))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 21).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 16) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 21).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 21)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 21)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 16) representative_mem words basis_eq

end C16

namespace C17

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2,5]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 17 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 22).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 22).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 17))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 22).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 17) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 22).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 22)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 22)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 17) representative_mem words basis_eq

end C17

namespace C18

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 18 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 23).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 23).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 18))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 23).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 18) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 23).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 23)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 23)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 18) representative_mem words basis_eq

end C18

namespace C19

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 19 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 24).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 24).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 19))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 24).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 19) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 24).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 24)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 24)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 19) representative_mem words basis_eq

end C19

namespace C20

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 20 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 26).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 26).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 20))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 26).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 20) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 26).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 26)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 26)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 20) representative_mem words basis_eq

end C20

namespace C21

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 21 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 27).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 27).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 21))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 27).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 21) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 27).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 27)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 27)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 21) representative_mem words basis_eq

end C21

namespace C22

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 22 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 28).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 28).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 22))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 28).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 22) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 28).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 28)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 28)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 22) representative_mem words basis_eq

end C22

namespace C23

private def words (j : Fin 9) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,4]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 23 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 30).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 30).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 23))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 30).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 23) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 30).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 30)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 30)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 23) representative_mem words basis_eq

end C23

namespace C24

private def words (j : Fin 9) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 24 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 31).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 31).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 24))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 31).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 24) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 31).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 31)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 31)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 24) representative_mem words basis_eq

end C24

namespace C25

private def words (j : Fin 9) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,1]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,4]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 25 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 32).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 32).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 25))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 32).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 25) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 32).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 32)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 32)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 25) representative_mem words basis_eq

end C25

namespace C26

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,2]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,2,5]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 26 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 35).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 35).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 26))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 35).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 26) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 35).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 35)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 35)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 26) representative_mem words basis_eq

end C26

namespace C27

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,2,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 27 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 36).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 36).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 27))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 36).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 27) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 36).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 36)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 36)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 27) representative_mem words basis_eq

end C27

namespace C28

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,2]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,2,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,2,5]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 28 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 37).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 37).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 28))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 37).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 28) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 37).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 37)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 37)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 28) representative_mem words basis_eq

end C28

namespace C29

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 29 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 40).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 40).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 29))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 40).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 29) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 40).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 40)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 40)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 29) representative_mem words basis_eq

end C29

namespace C30

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 30 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 41).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 41).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 30))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 41).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 30) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 41).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 41)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 41)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 30) representative_mem words basis_eq

end C30

namespace C31

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 31 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 42).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 42).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 31))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 42).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 31) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 42).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 42)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 42)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 31) representative_mem words basis_eq

end C31

namespace C32

private def words (j : Fin 14) : List Source := (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1,0]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1]])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1,2]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []]))) else (if j.val < 10 then (if j.val < 8 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,3]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [4]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1,0]])) else (if j.val < 12 then (if j.val < 11 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 13 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [3,4]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,4]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 32 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 47).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 47).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 32))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 47).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 32) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 47).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 47)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 47)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 32) representative_mem words basis_eq

end C32

namespace C33

private def words (j : Fin 16) : List Source := (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,2]]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,1,5]]) else (if j.val < 11 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [2,5],PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,0,5]])) else (if j.val < 14 then (if j.val < 13 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,5]]) else (if j.val < 15 then [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [1,2,5]] else [PrimitiveAffineEightFrameRow2ModuleOrbitsData.sourceWord [0,2,5]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 33 ∈
      (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 48).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 48).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow2ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 33))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 48).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 33) := by
  rw [PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.charts 48).2
    PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states 48)
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states_space 48)
    (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative 33) representative_mem words basis_eq

end C33

theorem canonical_span (i : Fin 34) :
    (PrimitiveAffineEightFrameRow2ModuleRepresentation.states (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicState i)).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow2ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow2ModuleOrbitsData.cyclicRepresentative i) := by
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
  · exact C22.span_eq
  · exact C23.span_eq
  · exact C24.span_eq
  · exact C25.span_eq
  · exact C26.span_eq
  · exact C27.span_eq
  · exact C28.span_eq
  · exact C29.span_eq
  · exact C30.span_eq
  · exact C31.span_eq
  · exact C32.span_eq
  · exact C33.span_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ModuleOrbitsCanonical

end
