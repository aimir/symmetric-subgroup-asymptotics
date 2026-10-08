import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleOrbitsData

/-! Selected row 24 canonical cyclic spans. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleOrbitsCanonical

abbrev Source := PrimitiveAffineEightFrameRow24ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop15TopCertificate.group

namespace C0

private def words (j : Fin 0) : List Source := []

private theorem representative_mem :
    PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 0 ∈
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 0).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 0).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow24ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 0))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 0).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 0) := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 0).2
    PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 0)
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space 0)
    (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 0) representative_mem words basis_eq

end C0

namespace C1

private def words (j : Fin 2) : List Source := (if j.val < 1 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4]])

private theorem representative_mem :
    PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 1 ∈
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 1).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 1).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow24ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 1))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 1).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 1) := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 1).2
    PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 1)
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space 1)
    (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 1) representative_mem words basis_eq

end C1

namespace C2

private def words (j : Fin 3) : List Source := (if j.val < 1 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 2 ∈
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 2).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 2).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow24ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 2))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 2).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 2) := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 2).2
    PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 2)
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space 2)
    (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 2) representative_mem words basis_eq

end C2

namespace C3

private def words (j : Fin 4) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord []]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 3 ∈
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 3).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 3).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow24ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 3))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 3).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 3) := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 3).2
    PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 3)
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space 3)
    (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 3) representative_mem words basis_eq

end C3

namespace C4

private def words (j : Fin 4) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 4 ∈
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 4).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 4).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow24ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 4))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 4).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 4) := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 4).2
    PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 4)
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space 4)
    (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 4) representative_mem words basis_eq

end C4

namespace C5

private def words (j : Fin 5) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4,3]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,4]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 5 ∈
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 5).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 5).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow24ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 5))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 5).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 5) := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 5).2
    PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 5)
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space 5)
    (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 5) representative_mem words basis_eq

end C5

namespace C6

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4,3]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,4,3]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,4,3]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4,3]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 6 ∈
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 6).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 6).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow24ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 6))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 6).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 6) := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 6).2
    PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 6)
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space 6)
    (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 6) representative_mem words basis_eq

end C6

namespace C7

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4,3]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3,4]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,4]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 7 ∈
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 7).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 7).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow24ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 7))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 7).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 7) := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 7).2
    PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 7)
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space 7)
    (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 7) representative_mem words basis_eq

end C7

namespace C8

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [2,4]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1,4]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 8 ∈
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 8).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 8).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow24ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 8))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 8).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 8) := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 8).2
    PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 8)
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space 8)
    (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 8) representative_mem words basis_eq

end C8

namespace C9

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [2,4]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1,4]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 9 ∈
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 9).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 9).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow24ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 9))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 9).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 9) := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 9).2
    PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 9)
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space 9)
    (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 9) representative_mem words basis_eq

end C9

namespace C10

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1,4]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,4]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1,4]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [2,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,4]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1,4]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,4]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,4]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1,4]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,4]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,4]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 10 ∈
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 10).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 10).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow24ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 10))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 10).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 10) := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 10).2
    PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 10)
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space 10)
    (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 10) representative_mem words basis_eq

end C10

namespace C11

private def words (j : Fin 11) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4,3]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1,3]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord []]))) else (if j.val < 8 then (if j.val < 6 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1]] else (if j.val < 7 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3]])) else (if j.val < 9 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3]] else (if j.val < 10 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1,3,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1,3,3]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 11 ∈
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 11).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 11).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow24ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 11))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 11).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 11) := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 11).2
    PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 11)
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space 11)
    (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 11) representative_mem words basis_eq

end C11

namespace C12

private def words (j : Fin 12) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,3,3]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,3,3]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord []]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3,3]])) else (if j.val < 10 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3]] else (if j.val < 11 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,3,3,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 12 ∈
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 12).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 12).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow24ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 12))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 12).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 12) := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 12).2
    PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 12)
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space 12)
    (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 12) representative_mem words basis_eq

end C12

namespace C13

private def words (j : Fin 12) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4,3]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1,3]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1,3]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3]]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3]])) else (if j.val < 10 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3]] else (if j.val < 11 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [1,3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [2,3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 13 ∈
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 13).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 13).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow24ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 13))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 13).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 13) := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 13).2
    PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 13)
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space 13)
    (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 13) representative_mem words basis_eq

end C13

namespace C14

private def words (j : Fin 13) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4,3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord []])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [2]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [2,4]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4,3]]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,4]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,3,4]])) else (if j.val < 11 then (if j.val < 10 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4]]) else (if j.val < 12 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [2,3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 14 ∈
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 14).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 14).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow24ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 14))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 14).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 14) := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 14).2
    PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 14)
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space 14)
    (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 14) representative_mem words basis_eq

end C14

namespace C15

private def words (j : Fin 14) : List Source := (if j.val < 7 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4,3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4,3]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4,3]])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [2,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4,3]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,4,3]]))) else (if j.val < 10 then (if j.val < 8 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,4,3]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4,3,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4,3,3]])) else (if j.val < 12 then (if j.val < 11 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4,3]]) else (if j.val < 13 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [2,3],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,4],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4,3]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 15 ∈
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 15).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 15).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow24ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 15))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 15).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 15) := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 15).2
    PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 15)
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space 15)
    (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 15) representative_mem words basis_eq

end C15

namespace C16

private def words (j : Fin 16) : List Source := (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4,3]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4,3]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3,4]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,3,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,3,3,4]]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,4]]) else (if j.val < 11 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,3,4]])) else (if j.val < 14 then (if j.val < 13 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [3,3,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [4]]) else (if j.val < 15 then [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,3,3,3]] else [PrimitiveAffineEightFrameRow24ModuleOrbitsData.sourceWord [0,4]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 16 ∈
      (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 16).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 16).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow24ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 16))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 16).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 16) := by
  rw [PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.charts 16).2
    PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states 16)
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states_space 16)
    (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative 16) representative_mem words basis_eq

end C16

theorem canonical_span (i : Fin 17) :
    (PrimitiveAffineEightFrameRow24ModuleRepresentation.states (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicState i)).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow24ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow24ModuleOrbitsData.cyclicRepresentative i) := by
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

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow24ModuleOrbitsCanonical

end
