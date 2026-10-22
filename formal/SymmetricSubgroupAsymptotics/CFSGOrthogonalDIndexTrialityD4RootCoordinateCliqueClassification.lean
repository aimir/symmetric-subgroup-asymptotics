import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NeighborCoordinateAxes

/-! Every actual global maximal clique through the root is a full
original coordinate-axis completion, with an actual neighbour anchor. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDIndexPlaneFamilyAction CFSGOrthogonalDIndexTrialityD2Coordinates
open CFSGOrthogonalDIndexTrialityD4HammingTwins CFSGOrthogonalDIndexTrialityD4RootedCliques
variable (K : Type) [Field K] [Finite K]

local instance trialityD4CoordinateCliqueRootNontrivial : Nontrivial (RootPoints K) := rootPoints_nontrivial K
local instance trialityD4CoordinateCliqueRulingNontrivial : Nontrivial (RulingParameters K) := by
  have hc := rulingParameter_card K
  letI : Finite (RulingParameters K) := Nat.finite_of_card_ne_zero (by rw [hc]; omega)
  apply Finite.one_lt_card_iff_nontrivial.mp
  rw [hc]
  have hp : 0 < Nat.card K := Nat.card_pos
  omega

theorem maximal_root_clique_is_coordinate (T : Set (SingularPlanes K 0))
    (hT : MaximalClique (originalPlaneAdjacent K) T) (hx : originalRootPlane K ∈ T) :
    ∃ N : Neighbors K, ∃ i : Fin 3, T = rootCoordinateClique K N i := by
  let S : Set (Neighbors K) := {N | neighborAsPlane K N ∈ T}
  have he : T = rootCompletedClique K S := original_clique_root_completion K T hT.1 hx
  have hm : MaximalNeighborClique K S := (rootCompleted_maximal_iff K S).mp (he ▸ hT)
  have hcl : ∀ A, NeighborClique K A ↔ PullbackClique (neighborFlagMap K) A := by
    intro A
    constructor
    · intro h x hx y hy
      exact (neighbor_closed_adj_iff K x y).mp (h x hx y hy)
    · intro h x hx y hy
      exact (neighbor_closed_adj_iff K x y).mpr (h x hx y hy)
  have hmp : MaximalPullbackClique (neighborFlagMap K) S :=
    ⟨(hcl S).mp hm.1, fun A hA hSA => hm.2 A ((hcl A).mpr hA) hSA⟩
  obtain ⟨N, _, h0 | h1 | h2⟩ := maximal_pullback_eq_axis (neighborFlagMap K)
    (neighborFlagMap_surjective K) S hmp
  · exact ⟨N, 0, he.trans (congrArg (rootCompletedClique K)
      (h0.trans (neighbor_coordinate_axis_zero K N).symm))⟩
  · exact ⟨N, 1, he.trans (congrArg (rootCompletedClique K)
      (h1.trans (neighbor_coordinate_axis_one K N).symm))⟩
  · exact ⟨N, 2, he.trans (congrArg (rootCompletedClique K)
      (h2.trans (neighbor_coordinate_axis_two K N).symm))⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
