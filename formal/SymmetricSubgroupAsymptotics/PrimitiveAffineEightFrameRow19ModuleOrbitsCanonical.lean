import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleOrbitsData

/-! Selected row 19 canonical cyclic spans. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleOrbitsCanonical

abbrev Source := PrimitiveAffineEightFrameRow19ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop10TopCertificate.group

namespace C0

private def words (j : Fin 0) : List Source := []

private theorem representative_mem :
    PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 0 ∈
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 0).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 0).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow19ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 0))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 0).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 0) := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 0).2
    PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 0)
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space 0)
    (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 0) representative_mem words basis_eq

end C0

namespace C1

private def words (j : Fin 4) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [8]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,8]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 1 ∈
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 1).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 1).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow19ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 1))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 1).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 1) := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 1).2
    PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 1)
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space 1)
    (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 1) representative_mem words basis_eq

end C1

namespace C2

private def words (j : Fin 5) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [2]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord []] else (if j.val < 4 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [4]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [5]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 2 ∈
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 2).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 2).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow19ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 2))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 2).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 2) := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 2).2
    PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 2)
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space 2)
    (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 2) representative_mem words basis_eq

end C2

namespace C3

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [2]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [8]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [8],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [1,8]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [8],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [1,8],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [2,8]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 3 ∈
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 3).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 3).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow19ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 3))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 3).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 3) := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 3).2
    PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 3)
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space 3)
    (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 3) representative_mem words basis_eq

end C3

namespace C4

private def words (j : Fin 7) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [7]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [7]])) else (if j.val < 5 then (if j.val < 4 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [6]]) else (if j.val < 6 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [6]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 4 ∈
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 4).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 4).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow19ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 4))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 4).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 4) := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 4).2
    PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 4)
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space 4)
    (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 4) representative_mem words basis_eq

end C4

namespace C5

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [7]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [7]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [8]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [8],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [1,8],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [7,8]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [2,8]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [7,8]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 5 ∈
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 5).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 5).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow19ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 5))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 5).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 5) := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 5).2
    PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 5)
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space 5)
    (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 5) representative_mem words basis_eq

end C5

namespace C6

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [2]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [8]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [8],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,8]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [2,8]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [8],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,8],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [1,8],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [2,8]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 6 ∈
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 6).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 6).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow19ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 6))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 6).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 6) := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 6).2
    PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 6)
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space 6)
    (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 6) representative_mem words basis_eq

end C6

namespace C7

private def words (j : Fin 9) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,2]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [3]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [3,3]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [3,5]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [3,3],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [3,5]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 7 ∈
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 7).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 7).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow19ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 7))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 7).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 7) := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 7).2
    PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 7)
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space 7)
    (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 7) representative_mem words basis_eq

end C7

namespace C8

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,0],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,2]]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [8]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,8]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [8],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,0,8]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,2,8]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [8],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,8],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [1,8],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,0,8],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,2,8]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 8 ∈
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 8).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 8).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow19ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 8))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 8).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 8) := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 8).2
    PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 8)
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space 8)
    (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 8) representative_mem words basis_eq

end C8

namespace C9

private def words (j : Fin 11) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [7]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [7],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [7],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [7],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,2]]))) else (if j.val < 8 then (if j.val < 6 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord []] else (if j.val < 7 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [6]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [6],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [3,3]])) else (if j.val < 9 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [3]] else (if j.val < 10 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [6],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [3,3]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [6],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [3,5]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 9 ∈
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 9).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 9).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow19ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 9))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 9).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 9) := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 9).2
    PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 9)
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space 9)
    (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 9) representative_mem words basis_eq

end C9

namespace C10

private def words (j : Fin 12) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [7]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [7],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [7],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,0]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [7],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,2]]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [8]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [7,8]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [8],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,8],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [7,8],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,0,8]])) else (if j.val < 10 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,8]] else (if j.val < 11 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [8],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,8],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [1,8],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [7,8],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,0,8]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [7,8],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,2,8]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 10 ∈
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 10).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 10).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow19ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 10))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 10).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 10) := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 10).2
    PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 10)
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space 10)
    (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 10) representative_mem words basis_eq

end C10

namespace C11

private def words (j : Fin 16) : List Source := (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [7]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,7]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,2]]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [8]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [7,8]]) else (if j.val < 11 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [2,8]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [2,8],PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,0,8]])) else (if j.val < 14 then (if j.val < 13 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [1,8]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,8]]) else (if j.val < 15 then [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,7,8]] else [PrimitiveAffineEightFrameRow19ModuleOrbitsData.sourceWord [0,2,8]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 11 ∈
      (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 11).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 11).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow19ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 11))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 11).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 11) := by
  rw [PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.charts 11).2
    PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states 11)
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states_space 11)
    (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative 11) representative_mem words basis_eq

end C11

theorem canonical_span (i : Fin 12) :
    (PrimitiveAffineEightFrameRow19ModuleRepresentation.states (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicState i)).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow19ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow19ModuleOrbitsData.cyclicRepresentative i) := by
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

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow19ModuleOrbitsCanonical

end
