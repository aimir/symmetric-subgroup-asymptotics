import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleOrbitsData

/-! Selected row 12 canonical cyclic spans. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleOrbitsCanonical

abbrev Source := PrimitiveAffineEightFrameRow12ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop8TopCertificate.group

namespace C0

private def words (j : Fin 0) : List Source := []

private theorem representative_mem :
    PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 0 ∈
      (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 0).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 0).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow12ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 0))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states 0).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 0) := by
  rw [PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 0).2
    PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states 0)
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space 0)
    (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 0) representative_mem words basis_eq

end C0

namespace C1

private def words (j : Fin 4) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [7]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,7]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 1 ∈
      (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 1).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 1).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow12ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 1))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states 1).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 1) := by
  rw [PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 1).2
    PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states 1)
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space 1)
    (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 1) representative_mem words basis_eq

end C1

namespace C2

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [3]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord []])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [6]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [5]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 2 ∈
      (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 2).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 2).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow12ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 2))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states 2).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 2) := by
  rw [PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 2).2
    PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states 2)
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space 2)
    (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 2) representative_mem words basis_eq

end C2

namespace C3

private def words (j : Fin 6) : List Source := (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [2]] else (if j.val < 2 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord []])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [6]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [5],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [6]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 3 ∈
      (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 3).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 3).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow12ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 3))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states 3).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 3) := by
  rw [PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 3).2
    PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states 3)
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space 3)
    (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 3) representative_mem words basis_eq

end C3

namespace C4

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [2]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [7]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,7]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [3,7]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [7],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,7],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [2,7]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 4 ∈
      (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 4).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 4).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow12ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 4))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states 4).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 4) := by
  rw [PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 4).2
    PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states 4)
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space 4)
    (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 4) representative_mem words basis_eq

end C4

namespace C5

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [3]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [7]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,7]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [3,7]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,7],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [2,7],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [3,7]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 5 ∈
      (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 5).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 5).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow12ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 5))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states 5).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 5) := by
  rw [PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 5).2
    PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states 5)
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space 5)
    (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 5) representative_mem words basis_eq

end C5

namespace C6

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [2,4]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [2,4]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [4]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [7]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [7],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,5]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 6 ∈
      (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 6).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 6).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow12ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 6))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states 6).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 6) := by
  rw [PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 6).2
    PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states 6)
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space 6)
    (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 6) representative_mem words basis_eq

end C6

namespace C7

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,1]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,2]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord []]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [4]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,4]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,5]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 7 ∈
      (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 7).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 7).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow12ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 7))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states 7).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 7) := by
  rw [PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 7).2
    PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states 7)
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space 7)
    (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 7) representative_mem words basis_eq

end C7

namespace C8

private def words (j : Fin 10) : List Source := (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,1]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [2]] else (if j.val < 4 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord []]))) else (if j.val < 7 then (if j.val < 6 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [4]]) else (if j.val < 8 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,4]] else (if j.val < 9 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [4],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [5]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,4],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,5]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 8 ∈
      (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 8).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 8).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow12ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 8))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states 8).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 8) := by
  rw [PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 8).2
    PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states 8)
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space 8)
    (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 8) representative_mem words basis_eq

end C8

namespace C9

private def words (j : Fin 12) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [1]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,1]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [1],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,1],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,2]]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [7]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,7]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [1,7]])) else (if j.val < 10 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,1,7]] else (if j.val < 11 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [1,7],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [2,7]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,1,7],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,2,7]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 9 ∈
      (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 9).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 9).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow12ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 9))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states 9).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 9) := by
  rw [PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 9).2
    PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states 9)
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space 9)
    (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 9) representative_mem words basis_eq

end C9

namespace C10

private def words (j : Fin 16) : List Source := (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [4]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [1,0]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [1,3]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,2]]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [7]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [7],PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [4,7]]) else (if j.val < 11 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [3,7]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,7]])) else (if j.val < 14 then (if j.val < 13 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [1,7]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [1,0,7]]) else (if j.val < 15 then [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [1,3,7]] else [PrimitiveAffineEightFrameRow12ModuleOrbitsData.sourceWord [0,2,7]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 10 ∈
      (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 10).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 10).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow12ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 10))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states 10).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 10) := by
  rw [PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.charts 10).2
    PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states 10)
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states_space 10)
    (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative 10) representative_mem words basis_eq

end C10

theorem canonical_span (i : Fin 11) :
    (PrimitiveAffineEightFrameRow12ModuleRepresentation.states (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicState i)).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow12ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow12ModuleOrbitsData.cyclicRepresentative i) := by
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

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow12ModuleOrbitsCanonical

end
