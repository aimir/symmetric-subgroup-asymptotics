import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NaturalCliqueAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4RootEdgeCliques

/-! Every ORIGINAL adjacent pair lies in a genuine global maximal
clique of EACH of the three natural types. These are the actual shared
edge witnesses used in the global-coherence argument. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDIndexPlaneFamilyAction CFSGOrthogonalDIndexTrialityD4RootedCliques
variable (K : Type) [Field K] [Finite K]

theorem every_edge_has_each_global_type (P Q : SingularPlanes K 0)
    (hPQ : originalPlaneAdjacent K P Q) (t : Fin 3) :
    ∃ T : Set (SingularPlanes K 0), MaximalClique (originalPlaneAdjacent K) T ∧
      P ∈ T ∧ Q ∈ T ∧ naturalCliqueType K T = t := by
  obtain ⟨g, hg⟩ := exists_natural_root_transporter K P
  let Q0 := naturalPlaneImage K g⁻¹ Q
  have h0 : originalPlaneAdjacent K (originalRootPlane K) Q0 := by
    have hh := naturalPlaneImage_adjacent K g⁻¹ hPQ
    rw [← hg, naturalPlaneImage_inv_cancel] at hh
    exact hh
  let N : Neighbors K := (neighborSubsetEquiv K).symm ⟨Q0, h0⟩
  obtain ⟨T0, hT0, hr, hN, ht⟩ := root_edge_has_each_global_type K N t
  refine ⟨naturalCliqueImage K g T0, naturalCliqueImage_maximal K g T0 hT0,
    ⟨originalRootPlane K, hr, hg⟩, ?_, ?_⟩
  · have hn : neighborAsPlane K N = Q0 := Subtype.ext rfl
    refine ⟨neighborAsPlane K N, hN, ?_⟩
    rw [hn]
    change naturalPlaneImage K g (naturalPlaneImage K g⁻¹ Q) = Q
    simpa only [inv_inv] using naturalPlaneImage_inv_cancel K g⁻¹ Q
  · exact (naturalImage_type_of_root_maximal_clique K g T0 hT0 hr).trans ht

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
