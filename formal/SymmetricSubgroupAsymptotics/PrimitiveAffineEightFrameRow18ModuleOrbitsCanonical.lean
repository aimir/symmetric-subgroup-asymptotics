import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow18ModuleOrbitsData

/-! Selected row 18 canonical cyclic spans. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow18ModuleOrbitsCanonical

abbrev Source := PrimitiveAffineEightFrameRow18ModuleOrbitsData.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop10TopCertificate.group

namespace C0

private def words (j : Fin 0) : List Source := []

private theorem representative_mem :
    PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicRepresentative 0 ∈
      (PrimitiveAffineEightFrameRow18ModuleRepresentation.charts 0).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.charts 0).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow18ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicRepresentative 0))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.states 0).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow18ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicRepresentative 0) := by
  rw [PrimitiveAffineEightFrameRow18ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.charts 0).2
    PrimitiveAffineEightFrameRow18ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.states 0)
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.states_space 0)
    (PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicRepresentative 0) representative_mem words basis_eq

end C0

namespace C1

private def words (j : Fin 4) : List Source := (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [3]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [8]] else [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [3,8]]))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicRepresentative 1 ∈
      (PrimitiveAffineEightFrameRow18ModuleRepresentation.charts 1).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.charts 1).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow18ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicRepresentative 1))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.states 1).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow18ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicRepresentative 1) := by
  rw [PrimitiveAffineEightFrameRow18ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.charts 1).2
    PrimitiveAffineEightFrameRow18ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.states 1)
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.states_space 1)
    (PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicRepresentative 1) representative_mem words basis_eq

end C1

namespace C2

private def words (j : Fin 8) : List Source := (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [2,3]] else [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [],PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [2],PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [2,3]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [0]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [8]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [4]] else [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [3],PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [8],PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [0,4]])))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicRepresentative 2 ∈
      (PrimitiveAffineEightFrameRow18ModuleRepresentation.charts 2).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.charts 2).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow18ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicRepresentative 2))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.states 2).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow18ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicRepresentative 2) := by
  rw [PrimitiveAffineEightFrameRow18ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.charts 2).2
    PrimitiveAffineEightFrameRow18ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.states 2)
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.states_space 2)
    (PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicRepresentative 2) representative_mem words basis_eq

end C2

namespace C3

private def words (j : Fin 12) : List Source := (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord []] else (if j.val < 2 then [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [3]] else [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [0]])) else (if j.val < 4 then [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [0,3]] else (if j.val < 5 then [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [0],PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [1]] else [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [0,3],PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [1,3]]))) else (if j.val < 9 then (if j.val < 7 then [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [8]] else (if j.val < 8 then [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [3,8]] else [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [0,8]])) else (if j.val < 10 then [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [0,3,8]] else (if j.val < 11 then [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [0,8],PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [1,8]] else [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [0,3,8],PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [1,3,8]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicRepresentative 3 ∈
      (PrimitiveAffineEightFrameRow18ModuleRepresentation.charts 3).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.charts 3).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow18ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicRepresentative 3))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.states 3).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow18ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicRepresentative 3) := by
  rw [PrimitiveAffineEightFrameRow18ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.charts 3).2
    PrimitiveAffineEightFrameRow18ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.states 3)
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.states_space 3)
    (PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicRepresentative 3) representative_mem words basis_eq

end C3

namespace C4

private def words (j : Fin 16) : List Source := (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord []] else [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [3]]) else (if j.val < 3 then [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [2]] else [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [2,3]])) else (if j.val < 6 then (if j.val < 5 then [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [0]] else [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [0,3]]) else (if j.val < 7 then [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [0,2]] else [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [0,2,3]]))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [8]] else [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [3,8]]) else (if j.val < 11 then [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [2,8]] else [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [2,3,8]])) else (if j.val < 14 then (if j.val < 13 then [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [0,8]] else [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [0,3,8]]) else (if j.val < 15 then [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [0,2,8]] else [PrimitiveAffineEightFrameRow18ModuleOrbitsData.sourceWord [0,2,3,8]]))))

private theorem representative_mem :
    PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicRepresentative 4 ∈
      (PrimitiveAffineEightFrameRow18ModuleRepresentation.charts 4).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.charts 4).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ PrimitiveAffineEightFrameRow18ModuleRepresentation.representation g
        (PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicRepresentative 4))).sum := by
  native_decide

theorem span_eq :
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.states 4).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow18ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicRepresentative 4) := by
  rw [PrimitiveAffineEightFrameRow18ModuleRepresentation.states_space]
  exact binaryCoordinate_eq_orbitSpan
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.charts 4).2
    PrimitiveAffineEightFrameRow18ModuleRepresentation.representation
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.states 4)
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.states_space 4)
    (PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicRepresentative 4) representative_mem words basis_eq

end C4

theorem canonical_span (i : Fin 5) :
    (PrimitiveAffineEightFrameRow18ModuleRepresentation.states (PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicState i)).toSubmodule =
      binaryOrbitSpan PrimitiveAffineEightFrameRow18ModuleRepresentation.representation
        (PrimitiveAffineEightFrameRow18ModuleOrbitsData.cyclicRepresentative i) := by
  fin_cases i
  · exact C0.span_eq
  · exact C1.span_eq
  · exact C2.span_eq
  · exact C3.span_eq
  · exact C4.span_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow18ModuleOrbitsCanonical

end
