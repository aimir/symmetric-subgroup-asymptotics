import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleOrbitsData

/-! Selected row 3 canonical cyclic spans. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleOrbitsCanonical

abbrev Source := PrimitiveAffineEightFrameRow3ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow3TopCertificate.group

namespace C0

private def words (j : Fin 0) : List Source := []

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 0 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 0).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 0).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 0))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 0).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 0) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 0).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 0)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 0)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 0) representative_mem words basis_eq

end C0

namespace C1

private def words (j : Fin 2) : List Source := (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0]])

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 1 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 1).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 1).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 1))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 1).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 1) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 1).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 1)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 1)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 1) representative_mem words basis_eq

end C1

namespace C2

private def words (j : Fin 2) : List Source := (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0]])

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 2 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 2).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 2).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 2))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 2).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 2) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 2).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 2)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 2)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 2) representative_mem words basis_eq

end C2

namespace C3

private def words (j : Fin 2) : List Source := (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0]])

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 3 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 3).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 3).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 3))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 3).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 3) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 3).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 3)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 3)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 3) representative_mem words basis_eq

end C3

namespace C4

private def words (j : Fin 4) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 4 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 4).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 4).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 4))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 4).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 4) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 4).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 4)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 4)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 4) representative_mem words basis_eq

end C4

namespace C5

private def words (j : Fin 5) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []] else (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 5 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 5).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 5).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 5))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 5).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 5) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 5).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 5)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 5)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 5) representative_mem words basis_eq

end C5

namespace C6

private def words (j : Fin 5) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []] else (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 6 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 6).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 6).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 6))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 6).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 6) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 6).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 6)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 6)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 6) representative_mem words basis_eq

end C6

namespace C7

private def words (j : Fin 5) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []] else (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 7 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 7).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 7).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 7))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 7).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 7) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 7).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 7)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 7)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 7) representative_mem words basis_eq

end C7

namespace C8

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2,5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1,5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2,5]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 8 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 8).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 8).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 8))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 8).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 8) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 8).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 8)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 8)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 8) representative_mem words basis_eq

end C8

namespace C9

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1,5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2,5]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 9 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 9).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 9).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 9))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 9).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 9) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 9).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 9)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 9)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 9) representative_mem words basis_eq

end C9

namespace C10

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1,5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2,5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1,5]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 10 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 10).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 10).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 10))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 10).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 10) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 10).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 10)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 10)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 10) representative_mem words basis_eq

end C10

namespace C11

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []] else (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 11 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 12).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 12).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 11))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 12).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 11) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 12).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 12)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 12)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 11) representative_mem words basis_eq

end C11

namespace C12

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 12 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 13).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 13).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 12))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 13).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 12) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 13).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 13)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 13)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 12) representative_mem words basis_eq

end C12

namespace C13

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 13 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 14).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 14).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 13))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 14).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 13) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 14).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 14)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 14)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 13) representative_mem words basis_eq

end C13

namespace C14

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 14 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 15).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 15).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 14))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 15).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 14) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 15).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 15)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 15)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 14) representative_mem words basis_eq

end C14

namespace C15

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 15 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 16).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 16).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 15))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 16).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 15) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 16).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 16)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 16)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 15) representative_mem words basis_eq

end C15

namespace C16

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 16 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 17).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 17).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 16))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 17).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 16) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 17).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 17)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 17)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 16) representative_mem words basis_eq

end C16

namespace C17

private def words (j : Fin 7) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 17 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 21).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 21).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 17))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 21).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 17) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 21).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 21)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 21)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 17) representative_mem words basis_eq

end C17

namespace C18

private def words (j : Fin 7) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,1]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 18 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 22).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 22).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 18))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 22).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 18) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 22).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 22)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 22)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 18) representative_mem words basis_eq

end C18

namespace C19

private def words (j : Fin 7) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,1]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 19 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 23).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 23).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 19))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 23).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 19) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 23).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 23)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 23)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 19) representative_mem words basis_eq

end C19

namespace C20

private def words (j : Fin 7) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 20 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 24).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 24).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 20))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 24).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 20) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 24).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 24)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 24)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 20) representative_mem words basis_eq

end C20

namespace C21

private def words (j : Fin 7) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 21 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 25).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 25).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 21))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 25).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 21) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 25).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 25)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 25)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 21) representative_mem words basis_eq

end C21

namespace C22

private def words (j : Fin 7) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,1]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 22 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 26).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 26).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 22))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 26).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 22) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 26).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 26)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 26)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 22) representative_mem words basis_eq

end C22

namespace C23

private def words (j : Fin 7) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 23 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 27).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 27).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 23))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 27).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 23) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 27).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 27)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 27)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 23) representative_mem words basis_eq

end C23

namespace C24

private def words (j : Fin 7) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 24 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 28).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 28).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 24))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 28).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 24) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 28).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 28)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 28)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 24) representative_mem words basis_eq

end C24

namespace C25

private def words (j : Fin 7) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,1]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 25 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 29).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 29).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 25))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 29).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 25) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 29).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 29)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 29)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 25) representative_mem words basis_eq

end C25

namespace C26

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 26 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 31).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 31).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 26))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 31).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 26) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 31).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 31)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 31)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 26) representative_mem words basis_eq

end C26

namespace C27

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 27 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 32).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 32).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 27))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 32).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 27) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 32).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 32)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 32)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 27) representative_mem words basis_eq

end C27

namespace C28

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 28 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 33).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 33).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 28))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 33).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 28) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 33).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 33)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 33)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 28) representative_mem words basis_eq

end C28

namespace C29

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2,5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1,5]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 29 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 34).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 34).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 29))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 34).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 29) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 34).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 34)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 34)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 29) representative_mem words basis_eq

end C29

namespace C30

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 30 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 35).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 35).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 30))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 35).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 30) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 35).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 35)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 35)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 30) representative_mem words basis_eq

end C30

namespace C31

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 31 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 36).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 36).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 31))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 36).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 31) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 36).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 36)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 36)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 31) representative_mem words basis_eq

end C31

namespace C32

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 32 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 37).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 37).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 32))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 37).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 32) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 37).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 37)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 37)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 32) representative_mem words basis_eq

end C32

namespace C33

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 33 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 38).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 38).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 33))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 38).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 33) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 38).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 38)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 38)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 33) representative_mem words basis_eq

end C33

namespace C34

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 34 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 39).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 39).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 34))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 39).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 34) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 39).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 39)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 39)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 34) representative_mem words basis_eq

end C34

namespace C35

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 35 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 40).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 40).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 35))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 40).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 35) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 40).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 40)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 40)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 35) representative_mem words basis_eq

end C35

namespace C36

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 36 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 41).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 41).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 36))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 41).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 36) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 41).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 41)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 41)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 36) representative_mem words basis_eq

end C36

namespace C37

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 37 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 43).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 43).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 37))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 43).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 37) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 43).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 43)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 43)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 37) representative_mem words basis_eq

end C37

namespace C38

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 38 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 44).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 44).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 38))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 44).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 38) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 44).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 44)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 44)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 38) representative_mem words basis_eq

end C38

namespace C39

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 39 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 45).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 45).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 39))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 45).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 39) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 45).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 45)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 45)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 39) representative_mem words basis_eq

end C39

namespace C40

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 40 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 46).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 46).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 40))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 46).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 40) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 46).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 46)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 46)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 40) representative_mem words basis_eq

end C40

namespace C41

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 41 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 48).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 48).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 41))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 48).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 41) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 48).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 48)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 48)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 41) representative_mem words basis_eq

end C41

namespace C42

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 42 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 49).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 49).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 42))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 49).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 42) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 49).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 49)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 49)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 42) representative_mem words basis_eq

end C42

namespace C43

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 43 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 50).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 50).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 43))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 50).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 43) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 50).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 50)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 50)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 43) representative_mem words basis_eq

end C43

namespace C44

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 44 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 51).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 51).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 44))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 51).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 44) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 51).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 51)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 51)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 44) representative_mem words basis_eq

end C44

namespace C45

private def words (j : Fin 9) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 45 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 56).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 56).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 45))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 56).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 45) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 56).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 56)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 56)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 45) representative_mem words basis_eq

end C45

namespace C46

private def words (j : Fin 9) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 46 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 57).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 57).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 46))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 57).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 46) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 57).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 57)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 57)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 46) representative_mem words basis_eq

end C46

namespace C47

private def words (j : Fin 9) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 47 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 58).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 58).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 47))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 58).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 47) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 58).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 58)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 58)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 47) representative_mem words basis_eq

end C47

namespace C48

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5,0]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5,0]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1,5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1,5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2,5]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 48 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 65).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 65).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 48))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 65).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 48) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 65).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 65)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 65)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 48) representative_mem words basis_eq

end C48

namespace C49

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5,0]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2,5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1,5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5,0]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 49 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 66).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 66).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 49))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 66).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 49) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 66).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 66)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 66)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 49) representative_mem words basis_eq

end C49

namespace C50

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5,0]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1,5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2,5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2,5]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 50 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 67).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 67).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 50))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 67).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 50) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 67).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 67)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 67)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 50) representative_mem words basis_eq

end C50

namespace C51

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5,0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 51 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 72).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 72).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 51))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 72).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 51) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 72).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 72)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 72)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 51) representative_mem words basis_eq

end C51

namespace C52

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5,0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 52 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 73).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 73).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 52))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 73).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 52) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 73).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 73)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 73)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 52) representative_mem words basis_eq

end C52

namespace C53

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5,0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5,0]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5,0]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 53 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 74).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 74).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 53))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 74).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 53) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 74).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 74)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 74)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 53) representative_mem words basis_eq

end C53

namespace C54

private def words (j : Fin 14) : List Source := (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1,2]])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []]))) else (if j.val < 10 then (if j.val < 8 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,3]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1,2]])) else (if j.val < 12 then (if j.val < 11 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2]]) else (if j.val < 13 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1,5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 54 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 79).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 79).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 54))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 79).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 54) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 79).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 79)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 79)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 54) representative_mem words basis_eq

end C54

namespace C55

private def words (j : Fin 14) : List Source := (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2]])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1,0]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []]))) else (if j.val < 10 then (if j.val < 8 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]])) else (if j.val < 12 then (if j.val < 11 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2]]) else (if j.val < 13 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3,4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 55 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 80).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 80).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 55))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 80).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 55) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 80).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 80)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 80)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 55) representative_mem words basis_eq

end C55

namespace C56

private def words (j : Fin 14) : List Source := (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1,0]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1,0]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []]))) else (if j.val < 10 then (if j.val < 8 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [4]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5]])) else (if j.val < 12 then (if j.val < 11 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2]]) else (if j.val < 13 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1,5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,4]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 56 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 81).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 81).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 56))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 81).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 56) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 81).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 81)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 81)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 56) representative_mem words basis_eq

end C56

namespace C57

private def words (j : Fin 16) : List Source := (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1,0]]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,2,5]]) else (if j.val < 11 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2,5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [2,5]])) else (if j.val < 14 then (if j.val < 13 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5,3]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [5,0]]) else (if j.val < 15 then [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1,5]] else [PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [1,5],PrimitiveAffineEightFrameRow3ModuleOrbitsData.sourceWord [0,5,3]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 57 ∈
      (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 82).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 82).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow3ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 57))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 82).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 57) := by
  rw [PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.charts 82).2
    PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states 82)
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states_space 82)
    (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative 57) representative_mem words basis_eq

end C57

theorem canonical_span (i : Fin 58) :
    (PrimitiveAffineEightFrameRow3ModuleRepresentation.states (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicState i)).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow3ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow3ModuleOrbitsData.cyclicRepresentative i) := by
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
  · exact C34.span_eq
  · exact C35.span_eq
  · exact C36.span_eq
  · exact C37.span_eq
  · exact C38.span_eq
  · exact C39.span_eq
  · exact C40.span_eq
  · exact C41.span_eq
  · exact C42.span_eq
  · exact C43.span_eq
  · exact C44.span_eq
  · exact C45.span_eq
  · exact C46.span_eq
  · exact C47.span_eq
  · exact C48.span_eq
  · exact C49.span_eq
  · exact C50.span_eq
  · exact C51.span_eq
  · exact C52.span_eq
  · exact C53.span_eq
  · exact C54.span_eq
  · exact C55.span_eq
  · exact C56.span_eq
  · exact C57.span_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ModuleOrbitsCanonical

end
