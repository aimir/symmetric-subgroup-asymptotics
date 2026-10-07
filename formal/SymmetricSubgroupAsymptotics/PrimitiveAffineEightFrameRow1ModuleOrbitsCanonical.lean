import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleOrbitsData

/-! Selected row 1 canonical cyclic spans. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleOrbitsCanonical

abbrev Source := PrimitiveAffineEightFrameRow1ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow1TopCertificate.group

namespace C0

private def words (j : Fin 0) : List Source := []

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 0 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 0).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 0).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 0))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 0).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 0) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 0).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 0)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 0)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 0) representative_mem words basis_eq

end C0

namespace C1

private def words (j : Fin 2) : List Source := (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]])

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 1 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 1).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 1).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 1))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 1).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 1) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 1).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 1)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 1)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 1) representative_mem words basis_eq

end C1

namespace C2

private def words (j : Fin 2) : List Source := (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]])

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 2 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 2).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 2).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 2))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 2).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 2) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 2).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 2)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 2)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 2) representative_mem words basis_eq

end C2

namespace C3

private def words (j : Fin 2) : List Source := (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]])

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 3 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 3).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 3).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 3))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 3).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 3) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 3).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 3)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 3)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 3) representative_mem words basis_eq

end C3

namespace C4

private def words (j : Fin 3) : List Source := (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 4 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 4).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 4).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 4))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 4).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 4) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 4).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 4)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 4)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 4) representative_mem words basis_eq

end C4

namespace C5

private def words (j : Fin 3) : List Source := (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 5 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 5).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 5).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 5))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 5).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 5) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 5).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 5)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 5)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 5) representative_mem words basis_eq

end C5

namespace C6

private def words (j : Fin 3) : List Source := (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 6 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 6).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 6).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 6))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 6).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 6) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 6).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 6)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 6)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 6) representative_mem words basis_eq

end C6

namespace C7

private def words (j : Fin 4) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 7 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 7).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 7).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 7))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 7).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 7) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 7).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 7)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 7)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 7) representative_mem words basis_eq

end C7

namespace C8

private def words (j : Fin 4) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 8 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 8).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 8).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 8))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 8).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 8) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 8).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 8)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 8)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 8) representative_mem words basis_eq

end C8

namespace C9

private def words (j : Fin 4) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 9 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 9).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 9).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 9))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 9).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 9) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 9).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 9)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 9)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 9) representative_mem words basis_eq

end C9

namespace C10

private def words (j : Fin 4) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 10 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 10).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 10).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 10))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 10).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 10) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 10).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 10)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 10)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 10) representative_mem words basis_eq

end C10

namespace C11

private def words (j : Fin 4) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 11 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 11).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 11).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 11))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 11).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 11) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 11).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 11)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 11)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 11) representative_mem words basis_eq

end C11

namespace C12

private def words (j : Fin 4) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 12 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 12).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 12).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 12))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 12).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 12) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 12).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 12)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 12)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 12) representative_mem words basis_eq

end C12

namespace C13

private def words (j : Fin 4) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 13 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 13).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 13).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 13))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 13).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 13) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 13).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 13)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 13)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 13) representative_mem words basis_eq

end C13

namespace C14

private def words (j : Fin 4) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 14 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 14).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 14).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 14))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 14).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 14) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 14).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 14)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 14)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 14) representative_mem words basis_eq

end C14

namespace C15

private def words (j : Fin 4) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 15 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 15).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 15).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 15))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 15).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 15) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 15).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 15)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 15)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 15) representative_mem words basis_eq

end C15

namespace C16

private def words (j : Fin 4) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 16 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 16).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 16).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 16))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 16).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 16) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 16).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 16)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 16)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 16) representative_mem words basis_eq

end C16

namespace C17

private def words (j : Fin 5) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 17 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 17).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 17).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 17))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 17).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 17) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 17).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 17)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 17)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 17) representative_mem words basis_eq

end C17

namespace C18

private def words (j : Fin 5) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 18 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 18).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 18).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 18))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 18).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 18) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 18).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 18)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 18)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 18) representative_mem words basis_eq

end C18

namespace C19

private def words (j : Fin 5) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 19 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 19).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 19).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 19))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 19).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 19) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 19).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 19)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 19)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 19) representative_mem words basis_eq

end C19

namespace C20

private def words (j : Fin 5) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 20 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 20).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 20).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 20))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 20).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 20) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 20).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 20)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 20)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 20) representative_mem words basis_eq

end C20

namespace C21

private def words (j : Fin 5) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 21 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 21).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 21).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 21))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 21).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 21) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 21).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 21)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 21)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 21) representative_mem words basis_eq

end C21

namespace C22

private def words (j : Fin 5) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 22 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 22).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 22).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 22))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 22).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 22) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 22).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 22)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 22)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 22) representative_mem words basis_eq

end C22

namespace C23

private def words (j : Fin 5) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 23 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 23).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 23).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 23))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 23).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 23) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 23).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 23)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 23)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 23) representative_mem words basis_eq

end C23

namespace C24

private def words (j : Fin 5) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 24 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 24).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 24).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 24))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 24).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 24) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 24).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 24)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 24)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 24) representative_mem words basis_eq

end C24

namespace C25

private def words (j : Fin 5) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 25 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 25).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 25).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 25))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 25).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 25) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 25).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 25)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 25)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 25) representative_mem words basis_eq

end C25

namespace C26

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 26 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 26).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 26).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 26))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 26).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 26) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 26).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 26)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 26)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 26) representative_mem words basis_eq

end C26

namespace C27

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 27 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 27).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 27).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 27))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 27).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 27) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 27).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 27)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 27)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 27) representative_mem words basis_eq

end C27

namespace C28

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 28 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 28).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 28).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 28))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 28).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 28) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 28).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 28)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 28)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 28) representative_mem words basis_eq

end C28

namespace C29

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 29 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 30).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 30).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 29))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 30).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 29) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 30).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 30)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 30)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 29) representative_mem words basis_eq

end C29

namespace C30

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 30 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 31).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 31).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 30))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 31).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 30) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 31).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 31)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 31)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 30) representative_mem words basis_eq

end C30

namespace C31

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 31 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 32).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 32).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 31))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 32).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 31) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 32).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 32)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 32)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 31) representative_mem words basis_eq

end C31

namespace C32

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 32 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 33).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 33).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 32))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 33).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 32) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 33).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 33)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 33)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 32) representative_mem words basis_eq

end C32

namespace C33

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 33 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 34).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 34).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 33))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 34).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 33) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 34).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 34)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 34)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 33) representative_mem words basis_eq

end C33

namespace C34

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 34 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 35).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 35).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 34))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 35).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 34) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 35).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 35)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 35)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 34) representative_mem words basis_eq

end C34

namespace C35

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 35 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 36).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 36).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 35))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 36).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 35) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 36).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 36)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 36)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 35) representative_mem words basis_eq

end C35

namespace C36

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 36 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 37).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 37).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 36))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 37).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 36) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 37).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 37)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 37)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 36) representative_mem words basis_eq

end C36

namespace C37

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 37 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 38).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 38).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 37))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 38).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 37) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 38).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 38)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 38)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 37) representative_mem words basis_eq

end C37

namespace C38

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 38 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 39).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 39).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 38))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 39).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 38) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 39).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 39)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 39)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 38) representative_mem words basis_eq

end C38

namespace C39

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 39 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 40).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 40).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 39))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 40).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 39) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 40).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 40)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 40)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 39) representative_mem words basis_eq

end C39

namespace C40

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 40 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 41).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 41).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 40))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 41).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 40) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 41).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 41)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 41)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 40) representative_mem words basis_eq

end C40

namespace C41

private def words (j : Fin 7) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 41 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 45).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 45).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 41))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 45).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 41) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 45).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 45)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 45)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 41) representative_mem words basis_eq

end C41

namespace C42

private def words (j : Fin 7) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 42 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 46).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 46).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 42))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 46).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 42) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 46).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 46)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 46)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 42) representative_mem words basis_eq

end C42

namespace C43

private def words (j : Fin 7) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 43 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 47).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 47).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 43))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 47).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 43) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 47).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 47)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 47)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 43) representative_mem words basis_eq

end C43

namespace C44

private def words (j : Fin 7) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 44 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 48).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 48).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 44))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 48).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 44) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 48).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 48)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 48)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 44) representative_mem words basis_eq

end C44

namespace C45

private def words (j : Fin 7) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 45 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 49).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 49).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 45))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 49).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 45) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 49).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 49)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 49)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 45) representative_mem words basis_eq

end C45

namespace C46

private def words (j : Fin 7) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 46 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 50).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 50).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 46))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 50).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 46) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 50).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 50)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 50)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 46) representative_mem words basis_eq

end C46

namespace C47

private def words (j : Fin 7) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 47 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 51).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 51).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 47))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 51).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 47) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 51).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 51)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 51)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 47) representative_mem words basis_eq

end C47

namespace C48

private def words (j : Fin 7) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 48 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 52).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 52).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 48))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 52).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 48) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 52).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 52)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 52)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 48) representative_mem words basis_eq

end C48

namespace C49

private def words (j : Fin 7) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 49 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 53).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 53).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 49))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 53).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 49) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 53).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 53)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 53)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 49) representative_mem words basis_eq

end C49

namespace C50

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 50 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 55).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 55).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 50))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 55).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 50) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 55).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 55)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 55)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 50) representative_mem words basis_eq

end C50

namespace C51

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 51 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 56).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 56).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 51))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 56).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 51) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 56).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 56)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 56)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 51) representative_mem words basis_eq

end C51

namespace C52

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 52 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 57).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 57).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 52))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 57).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 52) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 57).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 57)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 57)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 52) representative_mem words basis_eq

end C52

namespace C53

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 53 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 58).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 58).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 53))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 58).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 53) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 58).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 58)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 58)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 53) representative_mem words basis_eq

end C53

namespace C54

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 54 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 59).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 59).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 54))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 59).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 54) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 59).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 59)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 59)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 54) representative_mem words basis_eq

end C54

namespace C55

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 55 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 60).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 60).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 55))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 60).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 55) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 60).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 60)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 60)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 55) representative_mem words basis_eq

end C55

namespace C56

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 56 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 61).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 61).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 56))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 61).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 56) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 61).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 61)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 61)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 56) representative_mem words basis_eq

end C56

namespace C57

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 57 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 62).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 62).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 57))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 62).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 57) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 62).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 62)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 62)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 57) representative_mem words basis_eq

end C57

namespace C58

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 58 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 63).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 63).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 58))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 63).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 58) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 63).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 63)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 63)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 58) representative_mem words basis_eq

end C58

namespace C59

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 59 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 64).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 64).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 59))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 64).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 59) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 64).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 64)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 64)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 59) representative_mem words basis_eq

end C59

namespace C60

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 60 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 65).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 65).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 60))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 65).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 60) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 65).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 65)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 65)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 60) representative_mem words basis_eq

end C60

namespace C61

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 61 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 67).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 67).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 61))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 67).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 61) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 67).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 67)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 67)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 61) representative_mem words basis_eq

end C61

namespace C62

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 62 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 68).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 68).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 62))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 68).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 62) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 68).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 68)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 68)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 62) representative_mem words basis_eq

end C62

namespace C63

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 63 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 69).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 69).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 63))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 69).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 63) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 69).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 69)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 69)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 63) representative_mem words basis_eq

end C63

namespace C64

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 64 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 70).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 70).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 64))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 70).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 64) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 70).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 70)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 70)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 64) representative_mem words basis_eq

end C64

namespace C65

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 65 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 72).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 72).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 65))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 72).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 65) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 72).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 72)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 72)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 65) representative_mem words basis_eq

end C65

namespace C66

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 66 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 73).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 73).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 66))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 73).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 66) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 73).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 73)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 73)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 66) representative_mem words basis_eq

end C66

namespace C67

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 67 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 74).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 74).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 67))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 74).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 67) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 74).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 74)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 74)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 67) representative_mem words basis_eq

end C67

namespace C68

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 68 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 75).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 75).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 68))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 75).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 68) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 75).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 75)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 75)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 68) representative_mem words basis_eq

end C68

namespace C69

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 69 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 77).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 77).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 69))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 77).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 69) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 77).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 77)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 77)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 69) representative_mem words basis_eq

end C69

namespace C70

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 70 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 78).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 78).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 70))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 78).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 70) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 78).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 78)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 78)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 70) representative_mem words basis_eq

end C70

namespace C71

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 71 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 79).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 79).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 71))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 79).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 71) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 79).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 79)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 79)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 71) representative_mem words basis_eq

end C71

namespace C72

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 72 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 80).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 80).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 72))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 80).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 72) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 80).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 80)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 80)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 72) representative_mem words basis_eq

end C72

namespace C73

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 73 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 81).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 81).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 73))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 81).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 73) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 81).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 81)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 81)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 73) representative_mem words basis_eq

end C73

namespace C74

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 74 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 82).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 82).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 74))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 82).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 74) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 82).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 82)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 82)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 74) representative_mem words basis_eq

end C74

namespace C75

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 75 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 83).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 83).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 75))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 83).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 75) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 83).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 83)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 83)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 75) representative_mem words basis_eq

end C75

namespace C76

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 76 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 84).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 84).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 76))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 84).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 76) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 84).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 84)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 84)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 76) representative_mem words basis_eq

end C76

namespace C77

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 77 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 85).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 85).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 77))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 85).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 77) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 85).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 85)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 85)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 77) representative_mem words basis_eq

end C77

namespace C78

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 78 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 86).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 86).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 78))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 86).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 78) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 86).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 86)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 86)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 78) representative_mem words basis_eq

end C78

namespace C79

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 79 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 87).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 87).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 79))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 87).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 79) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 87).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 87)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 87)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 79) representative_mem words basis_eq

end C79

namespace C80

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 80 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 88).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 88).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 80))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 88).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 80) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 88).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 88)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 88)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 80) representative_mem words basis_eq

end C80

namespace C81

private def words (j : Fin 9) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 81 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 92).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 92).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 81))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 92).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 81) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 92).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 92)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 92)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 81) representative_mem words basis_eq

end C81

namespace C82

private def words (j : Fin 9) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 82 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 93).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 93).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 82))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 93).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 82) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 93).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 93)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 93)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 82) representative_mem words basis_eq

end C82

namespace C83

private def words (j : Fin 9) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 83 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 94).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 94).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 83))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 94).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 83) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 94).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 94)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 94)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 83) representative_mem words basis_eq

end C83

namespace C84

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,3]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,3]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 84 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 101).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 101).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 84))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 101).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 84) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 101).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 101)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 101)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 84) representative_mem words basis_eq

end C84

namespace C85

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,3]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,3]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,3]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 85 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 102).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 102).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 85))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 102).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 85) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 102).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 102)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 102)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 85) representative_mem words basis_eq

end C85

namespace C86

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,3]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 86 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 103).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 103).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 86))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 103).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 86) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 103).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 103)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 103)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 86) representative_mem words basis_eq

end C86

namespace C87

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 87 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 108).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 108).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 87))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 108).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 87) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 108).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 108)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 108)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 87) representative_mem words basis_eq

end C87

namespace C88

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 88 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 109).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 109).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 88))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 109).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 88) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 109).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 109)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 109)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 88) representative_mem words basis_eq

end C88

namespace C89

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 89 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 110).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 110).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 89))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 110).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 89) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 110).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 110)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 110)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 89) representative_mem words basis_eq

end C89

namespace C90

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 90 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 111).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 111).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 90))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 111).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 90) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 111).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 111)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 111)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 90) representative_mem words basis_eq

end C90

namespace C91

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 91 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 112).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 112).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 91))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 112).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 91) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 112).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 112)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 112)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 91) representative_mem words basis_eq

end C91

namespace C92

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 92 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 113).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 113).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 92))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 113).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 92) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 113).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 113)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 113)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 92) representative_mem words basis_eq

end C92

namespace C93

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 93 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 114).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 114).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 93))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 114).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 93) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 114).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 114)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 114)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 93) representative_mem words basis_eq

end C93

namespace C94

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 94 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 115).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 115).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 94))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 115).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 94) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 115).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 115)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 115)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 94) representative_mem words basis_eq

end C94

namespace C95

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 95 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 116).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 116).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 95))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 116).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 95) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 116).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 116)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 116)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 95) representative_mem words basis_eq

end C95

namespace C96

private def words (j : Fin 11) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]))) else (if j.val < 8 then (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]])) else (if j.val < 9 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else (if j.val < 10 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 96 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 120).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 120).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 96))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 120).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 96) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 120).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 120)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 120)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 96) representative_mem words basis_eq

end C96

namespace C97

private def words (j : Fin 11) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,1]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]))) else (if j.val < 8 then (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,1]])) else (if j.val < 9 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]] else (if j.val < 10 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 97 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 121).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 121).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 97))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 121).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 97) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 121).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 121)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 121)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 97) representative_mem words basis_eq

end C97

namespace C98

private def words (j : Fin 11) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]]))) else (if j.val < 8 then (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]])) else (if j.val < 9 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else (if j.val < 10 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 98 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 122).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 122).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 98))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 122).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 98) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 122).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 122)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 122)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 98) representative_mem words basis_eq

end C98

namespace C99

private def words (j : Fin 11) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]))) else (if j.val < 8 then (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0]] else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1]])) else (if j.val < 9 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else (if j.val < 10 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 99 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 123).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 123).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 99))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 123).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 99) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 123).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 123)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 123)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 99) representative_mem words basis_eq

end C99

namespace C100

private def words (j : Fin 11) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]]))) else (if j.val < 8 then (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1]])) else (if j.val < 9 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else (if j.val < 10 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 100 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 124).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 124).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 100))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 124).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 100) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 124).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 124)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 124)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 100) representative_mem words basis_eq

end C100

namespace C101

private def words (j : Fin 11) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]]))) else (if j.val < 8 then (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]] else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]])) else (if j.val < 9 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]] else (if j.val < 10 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 101 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 125).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 125).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 101))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 125).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 101) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 125).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 125)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 125)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 101) representative_mem words basis_eq

end C101

namespace C102

private def words (j : Fin 12) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]])) else (if j.val < 10 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else (if j.val < 11 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 102 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 127).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 127).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 102))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 127).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 102) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 127).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 127)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 127)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 102) representative_mem words basis_eq

end C102

namespace C103

private def words (j : Fin 12) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0]])) else (if j.val < 10 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else (if j.val < 11 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 103 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 128).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 128).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 103))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 128).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 103) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 128).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 128)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 128)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 103) representative_mem words basis_eq

end C103

namespace C104

private def words (j : Fin 12) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]])) else (if j.val < 10 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0]] else (if j.val < 11 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 104 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 129).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 129).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 104))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 129).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 104) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 129).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 129)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 129)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 104) representative_mem words basis_eq

end C104

namespace C105

private def words (j : Fin 12) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0]])) else (if j.val < 10 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else (if j.val < 11 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 105 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 130).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 130).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 105))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 130).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 105) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 130).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 130)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 130)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 105) representative_mem words basis_eq

end C105

namespace C106

private def words (j : Fin 12) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]])) else (if j.val < 10 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else (if j.val < 11 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 106 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 131).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 131).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 106))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 131).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 106) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 131).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 131)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 131)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 106) representative_mem words basis_eq

end C106

namespace C107

private def words (j : Fin 12) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]])) else (if j.val < 10 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else (if j.val < 11 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 107 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 132).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 132).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 107))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 132).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 107) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 132).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 132)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 132)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 107) representative_mem words basis_eq

end C107

namespace C108

private def words (j : Fin 12) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]])) else (if j.val < 10 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else (if j.val < 11 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 108 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 133).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 133).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 108))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 133).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 108) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 133).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 133)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 133)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 108) representative_mem words basis_eq

end C108

namespace C109

private def words (j : Fin 12) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]])) else (if j.val < 10 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else (if j.val < 11 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 109 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 134).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 134).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 109))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 134).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 109) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 134).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 134)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 134)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 109) representative_mem words basis_eq

end C109

namespace C110

private def words (j : Fin 12) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]])) else (if j.val < 10 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else (if j.val < 11 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 110 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 135).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 135).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 110))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 135).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 110) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 135).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 135)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 135)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 110) representative_mem words basis_eq

end C110

namespace C111

private def words (j : Fin 13) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0]])) else (if j.val < 11 then (if j.val < 10 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]]) else (if j.val < 12 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 111 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 136).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 136).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 111))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 136).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 111) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 136).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 136)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 136)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 111) representative_mem words basis_eq

end C111

namespace C112

private def words (j : Fin 13) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]])) else (if j.val < 11 then (if j.val < 10 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 12 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 112 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 137).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 137).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 112))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 137).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 112) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 137).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 137)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 137)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 112) representative_mem words basis_eq

end C112

namespace C113

private def words (j : Fin 13) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]])) else (if j.val < 11 then (if j.val < 10 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]]) else (if j.val < 12 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 113 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 138).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 138).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 113))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 138).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 113) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 138).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 138)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 138)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 113) representative_mem words basis_eq

end C113

namespace C114

private def words (j : Fin 14) : List Source := (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]]))) else (if j.val < 10 then (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]])) else (if j.val < 12 then (if j.val < 11 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 13 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 114 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 139).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 139).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 114))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 139).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 114) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 139).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 139)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 139)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 114) representative_mem words basis_eq

end C114

namespace C115

private def words (j : Fin 14) : List Source := (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0]])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]]))) else (if j.val < 10 then (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]])) else (if j.val < 12 then (if j.val < 11 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 13 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 115 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 140).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 140).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 115))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 140).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 115) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 140).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 140)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 140)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 115) representative_mem words basis_eq

end C115

namespace C116

private def words (j : Fin 14) : List Source := (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]]))) else (if j.val < 10 then (if j.val < 8 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]])) else (if j.val < 12 then (if j.val < 11 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0]]) else (if j.val < 13 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 116 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 141).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 141).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 116))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 141).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 116) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 141).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 141)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 141)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 116) representative_mem words basis_eq

end C116

namespace C117

private def words (j : Fin 16) : List Source := (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,2],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,2]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1]]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,1,3]]) else (if j.val < 11 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [2,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,0,3]])) else (if j.val < 14 then (if j.val < 13 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,1]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [3,0]]) else (if j.val < 15 then [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow1ModuleOrbitsData.sourceWord [1,3]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 117 ∈
      (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 142).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 142).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow1ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 117))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 142).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 117) := by
  rw [PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.charts 142).2
    PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states 142)
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states_space 142)
    (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative 117) representative_mem words basis_eq

end C117

theorem canonical_span (i : Fin 118) :
    (PrimitiveAffineEightFrameRow1ModuleRepresentation.states (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicState i)).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow1ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow1ModuleOrbitsData.cyclicRepresentative i) := by
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
  · exact C58.span_eq
  · exact C59.span_eq
  · exact C60.span_eq
  · exact C61.span_eq
  · exact C62.span_eq
  · exact C63.span_eq
  · exact C64.span_eq
  · exact C65.span_eq
  · exact C66.span_eq
  · exact C67.span_eq
  · exact C68.span_eq
  · exact C69.span_eq
  · exact C70.span_eq
  · exact C71.span_eq
  · exact C72.span_eq
  · exact C73.span_eq
  · exact C74.span_eq
  · exact C75.span_eq
  · exact C76.span_eq
  · exact C77.span_eq
  · exact C78.span_eq
  · exact C79.span_eq
  · exact C80.span_eq
  · exact C81.span_eq
  · exact C82.span_eq
  · exact C83.span_eq
  · exact C84.span_eq
  · exact C85.span_eq
  · exact C86.span_eq
  · exact C87.span_eq
  · exact C88.span_eq
  · exact C89.span_eq
  · exact C90.span_eq
  · exact C91.span_eq
  · exact C92.span_eq
  · exact C93.span_eq
  · exact C94.span_eq
  · exact C95.span_eq
  · exact C96.span_eq
  · exact C97.span_eq
  · exact C98.span_eq
  · exact C99.span_eq
  · exact C100.span_eq
  · exact C101.span_eq
  · exact C102.span_eq
  · exact C103.span_eq
  · exact C104.span_eq
  · exact C105.span_eq
  · exact C106.span_eq
  · exact C107.span_eq
  · exact C108.span_eq
  · exact C109.span_eq
  · exact C110.span_eq
  · exact C111.span_eq
  · exact C112.span_eq
  · exact C113.span_eq
  · exact C114.span_eq
  · exact C115.span_eq
  · exact C116.span_eq
  · exact C117.span_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ModuleOrbitsCanonical

end
