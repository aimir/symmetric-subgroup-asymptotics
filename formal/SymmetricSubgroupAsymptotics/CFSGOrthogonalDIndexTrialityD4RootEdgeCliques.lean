import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NaturalTypeTransport
import Mathlib.Tactic.FinCases

/-! The SAME original root-neighbour edge lies in three explicit
global maximal cliques, one of each constructed natural type. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDIndexPlaneFamilyAction CFSGOrthogonalDIndexTrialityD4RootedCliques
variable (K : Type) [Field K]

def rootEdgeClique (N : Neighbors K) (t : Fin 3) : Set (SingularPlanes K 0) :=
  Fin.cases (rootCompletedClique K (neighborTop K (neighborThreeSpace K N)))
    (Fin.cases (rootCompletedClique K (neighborColumnStar K (neighborPoint K N)
      (neighborOppositeParameters K N).1))
      (fun _ => rootCompletedClique K (neighborRowStar K (neighborPoint K N)
        (neighborOppositeParameters K N).2))) t

theorem rootEdgeClique_maximal [Finite K] (N : Neighbors K) (t : Fin 3) :
    MaximalClique (originalPlaneAdjacent K) (rootEdgeClique K N t) := by
  fin_cases t
  · exact completed_top_maximal K _
  · exact completed_columnStar_maximal K _ _
  · exact completed_rowStar_maximal K _ _

theorem rootEdgeClique_type (N : Neighbors K) (t : Fin 3) :
    naturalCliqueType K (rootEdgeClique K N t) = t := by
  fin_cases t
  · exact completed_top_type K _
  · exact completed_columnStar_type K _ _
  · exact completed_rowStar_type K _ _

theorem root_mem_rootEdgeClique (N : Neighbors K) (t : Fin 3) :
    originalRootPlane K ∈ rootEdgeClique K N t := by
  fin_cases t <;> exact Or.inl rfl

theorem neighbor_mem_rootEdgeClique (N : Neighbors K) (t : Fin 3) :
    neighborAsPlane K N ∈ rootEdgeClique K N t := by
  fin_cases t
  · apply (mem_rootCompletedClique_iff K _ _).mpr
    exact Or.inr ⟨N, neighbor_le_threeSpace K N, rfl⟩
  · apply (mem_rootCompletedClique_iff K _ _).mpr
    exact Or.inr ⟨N, (neighbor_point_column_iff_star K N _ _).mp ⟨rfl, rfl⟩, rfl⟩
  · apply (mem_rootCompletedClique_iff K _ _).mpr
    exact Or.inr ⟨N, (neighbor_point_row_iff_star K N _ _).mp ⟨rfl, rfl⟩, rfl⟩

theorem rootEdgeClique_injective (N : Neighbors K) : Function.Injective (rootEdgeClique K N) := by
  intro t u he
  have hh := congrArg (naturalCliqueType K) he
  rw [rootEdgeClique_type, rootEdgeClique_type] at hh
  exact hh

theorem root_edge_has_each_global_type [Finite K] (N : Neighbors K) (t : Fin 3) :
    ∃ T : Set (SingularPlanes K 0), MaximalClique (originalPlaneAdjacent K) T ∧
      originalRootPlane K ∈ T ∧ neighborAsPlane K N ∈ T ∧ naturalCliqueType K T = t :=
  ⟨rootEdgeClique K N t, rootEdgeClique_maximal K N t, root_mem_rootEdgeClique K N t,
    neighbor_mem_rootEdgeClique K N t, rootEdgeClique_type K N t⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
