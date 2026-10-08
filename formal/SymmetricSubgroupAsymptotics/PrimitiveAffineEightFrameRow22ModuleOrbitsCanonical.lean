import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleOrbitsData

/-! Selected row 22 canonical cyclic spans. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleOrbitsCanonical

abbrev Source := PrimitiveAffineEightFrameRow22ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop13TopCertificate.group

namespace C0

private def words (j : Fin 0) : List Source := []

private theorem representative_mem :
    PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 0 ∈
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 0).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 0).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow22ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 0))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 0).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 0) := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 0).2
    PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 0)
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space 0)
    (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 0) representative_mem words basis_eq

end C0

namespace C1

private def words (j : Fin 2) : List Source := (if j.val < 1 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4]])

private theorem representative_mem :
    PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 1 ∈
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 1).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 1).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow22ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 1))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 1).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 1) := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 1).2
    PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 1)
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space 1)
    (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 1) representative_mem words basis_eq

end C1

namespace C2

private def words (j : Fin 3) : List Source := (if j.val < 1 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 2 ∈
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 2).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 2).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow22ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 2))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 2).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 2) := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 2).2
    PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 2)
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space 2)
    (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 2) representative_mem words basis_eq

end C2

namespace C3

private def words (j : Fin 3) : List Source := (if j.val < 1 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 3 ∈
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 3).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 3).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow22ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 3))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 3).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 3) := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 3).2
    PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 3)
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space 3)
    (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 3) representative_mem words basis_eq

end C3

namespace C4

private def words (j : Fin 3) : List Source := (if j.val < 1 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 4 ∈
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 4).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 4).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow22ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 4))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 4).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 4) := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 4).2
    PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 4)
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space 4)
    (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 4) representative_mem words basis_eq

end C4

namespace C5

private def words (j : Fin 4) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 5 ∈
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 6).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 6).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow22ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 5))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 6).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 5) := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 6).2
    PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 6)
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space 6)
    (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 5) representative_mem words basis_eq

end C5

namespace C6

private def words (j : Fin 5) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 6 ∈
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 7).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 7).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow22ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 6))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 7).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 6) := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 7).2
    PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 7)
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space 7)
    (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 6) representative_mem words basis_eq

end C6

namespace C7

private def words (j : Fin 5) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 7 ∈
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 8).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 8).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow22ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 7))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 8).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 7) := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 8).2
    PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 8)
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space 8)
    (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 7) representative_mem words basis_eq

end C7

namespace C8

private def words (j : Fin 5) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 8 ∈
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 9).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 9).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow22ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 8))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 9).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 8) := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 9).2
    PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 9)
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space 9)
    (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 8) representative_mem words basis_eq

end C8

namespace C9

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5,4]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5,4,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 9 ∈
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 11).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 11).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow22ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 9))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 11).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 9) := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 11).2
    PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 11)
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space 11)
    (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 9) representative_mem words basis_eq

end C9

namespace C10

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [0,4]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [3]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [3,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord []]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2,4]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 10 ∈
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 12).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 12).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow22ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 10))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 12).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 10) := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 12).2
    PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 12)
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space 12)
    (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 10) representative_mem words basis_eq

end C10

namespace C11

private def words (j : Fin 11) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,5,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,5,4]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,4]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord []]))) else (if j.val < 8 then (if j.val < 6 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [3]] else (if j.val < 7 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2,5]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]])) else (if j.val < 9 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]] else (if j.val < 10 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,4,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,4,4]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 11 ∈
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 13).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 13).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow22ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 11))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 13).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 11) := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 13).2
    PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 13)
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space 13)
    (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 11) representative_mem words basis_eq

end C11

namespace C12

private def words (j : Fin 11) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,5,4]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,4]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord []]))) else (if j.val < 8 then (if j.val < 6 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2,5]] else (if j.val < 7 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4]])) else (if j.val < 9 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]] else (if j.val < 10 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,5]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,4,4]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 12 ∈
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 14).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 14).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow22ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 12))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 14).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 12) := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 14).2
    PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 14)
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space 14)
    (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 12) representative_mem words basis_eq

end C12

namespace C13

private def words (j : Fin 11) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,5,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord []]))) else (if j.val < 8 then (if j.val < 6 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2,5]] else (if j.val < 7 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2,5]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]])) else (if j.val < 9 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4]] else (if j.val < 10 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,4,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,5]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 13 ∈
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 15).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 15).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow22ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 13))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 15).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 13) := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 15).2
    PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 15)
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space 15)
    (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 13) representative_mem words basis_eq

end C13

namespace C14

private def words (j : Fin 12) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,5,4]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [3,5]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [3,5]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5]]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [3]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2,5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5]])) else (if j.val < 10 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5]] else (if j.val < 11 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2,4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 14 ∈
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 17).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 17).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow22ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 14))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 17).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 14) := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 17).2
    PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 17)
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space 17)
    (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 14) representative_mem words basis_eq

end C14

namespace C15

private def words (j : Fin 13) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,5,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord []])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2,5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,4,5]])) else (if j.val < 11 then (if j.val < 10 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4]]) else (if j.val < 12 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2,4]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 15 ∈
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 18).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 18).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow22ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 15))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 18).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 15) := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 18).2
    PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 18)
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space 18)
    (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 15) representative_mem words basis_eq

end C15

namespace C16

private def words (j : Fin 13) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,5,4]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord []])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,4]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5]]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2,5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,4,5]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2,5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]])) else (if j.val < 11 then (if j.val < 10 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]]) else (if j.val < 12 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2,4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 16 ∈
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 19).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 19).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow22ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 16))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 19).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 16) := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 19).2
    PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 19)
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space 19)
    (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 16) representative_mem words basis_eq

end C16

namespace C17

private def words (j : Fin 13) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,5,4]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,5,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord []])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,4]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5]]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,4,5]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2,5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,4,5]])) else (if j.val < 11 then (if j.val < 10 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]]) else (if j.val < 12 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [2,4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 17 ∈
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 20).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 20).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow22ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 17))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 20).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 17) := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 20).2
    PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 20)
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space 20)
    (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 17) representative_mem words basis_eq

end C17

namespace C18

private def words (j : Fin 16) : List Source := (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5,4]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,5,4]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5,4,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,4],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,5,4,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,4]]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,5]]) else (if j.val < 11 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,4,5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,4,5,4]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,4,5]])) else (if j.val < 14 then (if j.val < 13 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [4,4]]) else (if j.val < 15 then [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,5]] else [PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,5],PrimitiveAffineEightFrameRow22ModuleOrbitsData.sourceWord [1,4,4]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 18 ∈
      (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 22).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 22).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow22ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 18))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 22).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 18) := by
  rw [PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.charts 22).2
    PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states 22)
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states_space 22)
    (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative 18) representative_mem words basis_eq

end C18

theorem canonical_span (i : Fin 19) :
    (PrimitiveAffineEightFrameRow22ModuleRepresentation.states (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicState i)).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow22ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow22ModuleOrbitsData.cyclicRepresentative i) := by
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

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow22ModuleOrbitsCanonical

end
