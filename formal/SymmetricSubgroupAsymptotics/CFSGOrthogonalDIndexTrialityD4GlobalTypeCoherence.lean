import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4VertexTypeFormula
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4EveryEdgeTypes
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4TypeCoherence

/-! Genuine global triality type coherence on the SAME original D4
plane graph. Actual shared edge-cliques and proved connectedness make
the internally constructed local permutations agree everywhere. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexTrialityD4RootedCliques CFSGOrthogonalDIndexTrialityD4TypeCoherence
variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]

def GlobalMaximalCliques := {T : Set (SingularPlanes K 0) // MaximalClique (originalPlaneAdjacent K) T}

def automorphismGlobalClique (f : MulAut (elementaryProjective K 4))
    (T : GlobalMaximalCliques K) : GlobalMaximalCliques K :=
  ⟨automorphismCliqueImage K p f T.val, automorphismCliqueImage_maximal K p f T.val T.property⟩

theorem vertexTypePermutation_independent (f : MulAut (elementaryProjective K 4))
    (P Q : SingularPlanes K 0) : vertexTypePermutation K p f P = vertexTypePermutation K p f Q := by
  apply local_permutations_eq_of_path (originalPlaneAdjacent K)
    (fun P (T : GlobalMaximalCliques K) => P ∈ T.val)
    (fun T : GlobalMaximalCliques K => naturalCliqueType K T.val)
    (automorphismGlobalClique K p f) (vertexTypePermutation K p f)
    (fun P T hPT => vertex_clique_type_formula K p f P T.val T.property hPT) ?_ P Q
    (original_plane_graph_connected K P Q)
  intro V W hVW t
  obtain ⟨T, hT, hV, hW, ht⟩ := every_edge_has_each_global_type K V W hVW t
  exact ⟨⟨T, hT⟩, hV, hW, ht⟩

def globalTypePermutation (f : MulAut (elementaryProjective K 4)) : Equiv.Perm (Fin 3) :=
  vertexTypePermutation K p f (originalRootPlane K)

theorem global_clique_type_formula (f : MulAut (elementaryProjective K 4))
    (P : SingularPlanes K 0) (T : Set (SingularPlanes K 0))
    (hT : MaximalClique (originalPlaneAdjacent K) T) (hP : P ∈ T) :
    naturalCliqueType K (automorphismCliqueImage K p f T) =
      globalTypePermutation K p f (naturalCliqueType K T) := by
  have hh := vertex_clique_type_formula K p f P T hT hP
  rw [vertexTypePermutation_independent K p f P (originalRootPlane K)] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
