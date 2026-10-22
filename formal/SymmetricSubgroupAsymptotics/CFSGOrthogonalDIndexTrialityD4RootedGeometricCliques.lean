import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4CliqueEquivalence
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NeighborAxisMaximality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NaturalPlaneAction

/-! Exact global maximal cliques through the original D4 root plane
are obtained by adding that plane to one of its three actual geometric
neighbour-clique families. This does not yet assert global type coherence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexTrialityD2Coordinates
open CFSGOrthogonalDIndexTrialityD4RootedCliques
variable (K : Type) [Field K]

def rootCompletedClique (S : Set (Neighbors K)) : Set (SingularPlanes K 0) :=
  RootExtension (originalPlaneAdjacent K) (originalRootPlane K)
    ((neighborSubsetEquiv K).symm ⁻¹' S)

theorem rootCompleted_maximal_iff (S : Set (Neighbors K)) :
    MaximalClique (originalPlaneAdjacent K) (rootCompletedClique K S) ↔
      MaximalNeighborClique K S := by
  unfold rootCompletedClique
  rw [maximal_rootExtension_iff (originalPlaneAdjacent K)
    (fun {_ _} => originalPlaneAdjacent_symm K) (originalRootPlane K)
    (fun h => h.1 rfl)]
  exact maximal_clique_preimage_iff
    (fun a b : OriginalNeighborSubset K => originalPlaneAdjacent K a.val b.val)
    (NeighborAdjacent K) (neighborSubsetEquiv K).symm
    (fun a b => neighbor_adjacent_iff_quadratic K
      ((neighborSubsetEquiv K).symm a) ((neighborSubsetEquiv K).symm b)) S

theorem original_clique_root_completion (T : Set (SingularPlanes K 0))
    (hT : Clique (originalPlaneAdjacent K) T) (hx : originalRootPlane K ∈ T) :
    T = rootCompletedClique K {S : Neighbors K | neighborAsPlane K S ∈ T} := by
  exact clique_eq_rootExtension (originalPlaneAdjacent K) (originalRootPlane K) T hT hx

theorem maximal_original_clique_through_root_geometric [Finite K]
    (T : Set (SingularPlanes K 0)) (hT : MaximalClique (originalPlaneAdjacent K) T)
    (hx : originalRootPlane K ∈ T) :
    (∃ W : ThreeExtensions K, T = rootCompletedClique K (neighborTop K W)) ∨
      (∃ U : RootPoints K, ∃ p : RulingParameters K,
        T = rootCompletedClique K (neighborColumnStar K U p)) ∨
      (∃ U : RootPoints K, ∃ q : RulingParameters K,
        T = rootCompletedClique K (neighborRowStar K U q)) := by
  let S : Set (Neighbors K) := {S | neighborAsPlane K S ∈ T}
  have he : T = rootCompletedClique K S := original_clique_root_completion K T hT.1 hx
  have hm : MaximalNeighborClique K S := (rootCompleted_maximal_iff K S).mp (he ▸ hT)
  rcases maximal_neighbor_clique_geometric K S hm with ⟨W, hW⟩ | ⟨U, p, hp⟩ | ⟨U, q, hq⟩
  · exact Or.inl ⟨W, he.trans (congrArg (rootCompletedClique K) hW)⟩
  · exact Or.inr (Or.inl ⟨U, p, he.trans (congrArg (rootCompletedClique K) hp)⟩)
  · exact Or.inr (Or.inr ⟨U, q, he.trans (congrArg (rootCompletedClique K) hq)⟩)

theorem completed_top_maximal [Finite K] (W : ThreeExtensions K) :
    MaximalClique (originalPlaneAdjacent K) (rootCompletedClique K (neighborTop K W)) :=
  (rootCompleted_maximal_iff K _).mpr (neighborTop_maximal K W)

theorem completed_columnStar_maximal [Finite K] (U : RootPoints K) (p : RulingParameters K) :
    MaximalClique (originalPlaneAdjacent K) (rootCompletedClique K (neighborColumnStar K U p)) :=
  (rootCompleted_maximal_iff K _).mpr (neighborColumnStar_maximal K U p)

theorem completed_rowStar_maximal [Finite K] (U : RootPoints K) (q : RulingParameters K) :
    MaximalClique (originalPlaneAdjacent K) (rootCompletedClique K (neighborRowStar K U q)) :=
  (rootCompleted_maximal_iff K _).mpr (neighborRowStar_maximal K U q)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
