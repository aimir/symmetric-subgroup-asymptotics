import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NeighborAxisAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NaturalCliqueTypes
import Mathlib.Tactic.FinCases

/-! Full original coordinate axes have natural global types 0,2,1:
coordinate1 varies the column parameter and therefore fixes a ROW
maximal space. The fixed swap is kept explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDIndexTrialityD4HammingEdges CFSGOrthogonalDIndexTrialityD4HammingTwins
variable (K : Type) [Field K] [Finite K]

omit [Finite K] in
theorem neighbor_coordinate_axis_zero (N : Neighbors K) :
    neighborCoordinate K ⁻¹' CoordinateAxis (0 : Fin 3) (neighborCoordinate K N) =
      neighborFlagMap K ⁻¹' FirstAxis (neighborOppositeParameters K N).1
        (neighborOppositeParameters K N).2 := by
  ext S
  constructor
  · intro h
    exact ⟨(h (1 : Fin 3) (by decide)).symm, (h (2 : Fin 3) (by decide)).symm⟩
  · intro h j hj
    fin_cases j
    · exact False.elim (hj rfl)
    · exact h.1.symm
    · exact h.2.symm

omit [Finite K] in
theorem neighbor_coordinate_axis_one (N : Neighbors K) :
    neighborCoordinate K ⁻¹' CoordinateAxis (1 : Fin 3) (neighborCoordinate K N) =
      neighborFlagMap K ⁻¹' SecondAxis (neighborPoint K N) (neighborOppositeParameters K N).2 := by
  ext S
  constructor
  · intro h
    exact ⟨(h (0 : Fin 3) (by decide)).symm, (h (2 : Fin 3) (by decide)).symm⟩
  · intro h j hj
    fin_cases j
    · exact h.1.symm
    · exact False.elim (hj rfl)
    · exact h.2.symm

omit [Finite K] in
theorem neighbor_coordinate_axis_two (N : Neighbors K) :
    neighborCoordinate K ⁻¹' CoordinateAxis (2 : Fin 3) (neighborCoordinate K N) =
      neighborFlagMap K ⁻¹' ThirdAxis (neighborPoint K N) (neighborOppositeParameters K N).1 := by
  ext S
  constructor
  · intro h
    exact ⟨(h (0 : Fin 3) (by decide)).symm, (h (1 : Fin 3) (by decide)).symm⟩
  · intro h j hj
    fin_cases j
    · exact h.1.symm
    · exact h.2.symm
    · exact False.elim (hj rfl)

def coordinateTypePermutation : Equiv.Perm (Fin 3) := Equiv.swap 1 2

def rootCoordinateClique (N : Neighbors K) (i : Fin 3) :=
  rootCompletedClique K (neighborCoordinate K ⁻¹' CoordinateAxis i (neighborCoordinate K N))

theorem rootCoordinateClique_type (N : Neighbors K) (i : Fin 3) :
    naturalCliqueType K (rootCoordinateClique K N i) = coordinateTypePermutation i := by
  fin_cases i
  · change naturalCliqueType K (rootCompletedClique K
      (neighborCoordinate K ⁻¹' CoordinateAxis (0 : Fin 3) (neighborCoordinate K N))) =
        coordinateTypePermutation (0 : Fin 3)
    rw [neighbor_coordinate_axis_zero, flag_firstAxis_eq_top, completed_top_type]
    decide
  · change naturalCliqueType K (rootCompletedClique K
      (neighborCoordinate K ⁻¹' CoordinateAxis (1 : Fin 3) (neighborCoordinate K N))) =
        coordinateTypePermutation (1 : Fin 3)
    rw [neighbor_coordinate_axis_one, flag_secondAxis_eq_rowStar, completed_rowStar_type]
    decide
  · change naturalCliqueType K (rootCompletedClique K
      (neighborCoordinate K ⁻¹' CoordinateAxis (2 : Fin 3) (neighborCoordinate K N))) =
        coordinateTypePermutation (2 : Fin 3)
    rw [neighbor_coordinate_axis_two, flag_thirdAxis_eq_columnStar, completed_columnStar_type]
    decide

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
