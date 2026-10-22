import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NeighborCoordinateAxes

/-! The actual root stabilizer transports global root completions
through its actual original-neighbour action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]

def automorphismCliqueImage (f : MulAut (elementaryProjective K 4))
    (T : Set (SingularPlanes K 0)) : Set (SingularPlanes K 0) := singularActionHom K p 0 f '' T

theorem neighborAsPlane_stabilizer_action (f : originalRootStabilizer K p) (N : Neighbors K) :
    neighborAsPlane K (rootStabilizerNeighborHom K p f N) =
      singularActionHom K p 0 f.val (neighborAsPlane K N) := Subtype.ext rfl

theorem automorphismCliqueImage_rootCompleted (f : originalRootStabilizer K p)
    (S : Set (Neighbors K)) :
    automorphismCliqueImage K p f.val (rootCompletedClique K S) =
      rootCompletedClique K ((rootStabilizerNeighborHom K p f) '' S) := by
  ext P
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    apply (mem_rootCompletedClique_iff K _ _).mpr
    rcases (mem_rootCompletedClique_iff K S Q).mp hQ with rfl | ⟨N, hN, rfl⟩
    · exact Or.inl (originalRootStabilizer_fix K p f)
    · exact Or.inr ⟨rootStabilizerNeighborHom K p f N, ⟨N, hN, rfl⟩,
        neighborAsPlane_stabilizer_action K p f N⟩
  · intro hP
    rcases (mem_rootCompletedClique_iff K _ P).mp hP with rfl | ⟨N', hN', he⟩
    · exact ⟨originalRootPlane K, Or.inl rfl, originalRootStabilizer_fix K p f⟩
    · obtain ⟨N, hN, rfl⟩ := hN'
      refine ⟨neighborAsPlane K N, ?_, (neighborAsPlane_stabilizer_action K p f N).symm.trans he⟩
      exact (mem_rootCompletedClique_iff K S _).mpr (Or.inr ⟨N, hN, rfl⟩)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
