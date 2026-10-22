import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4RootCompletionAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4RootCoordinateCliqueClassification

/-! The ACTUAL original root stabilizer permutes the natural GLOBAL
clique types by a constructed homomorphism. The fixed direction/type
relabeling is conjugation by swap(1,2), not an extra hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexTrialityD4RootedCliques
variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]

def rootStabilizerTypeHom : originalRootStabilizer K p →* Equiv.Perm (Fin 3) :=
  (MulAut.conj coordinateTypePermutation).toMonoidHom.comp (rootStabilizerDirectionHom K p)

theorem rootStabilizer_image_coordinate_clique (f : originalRootStabilizer K p)
    (N : Neighbors K) (i : Fin 3) :
    automorphismCliqueImage K p f.val (rootCoordinateClique K N i) =
      rootCoordinateClique K (rootStabilizerNeighborHom K p f N) (rootStabilizerDirectionHom K p f i) := by
  unfold rootCoordinateClique
  rw [automorphismCliqueImage_rootCompleted, rootStabilizer_image_neighbor_axis,
    neighborCoordinate_equivariant]

theorem rootStabilizer_coordinate_type_formula (f : originalRootStabilizer K p)
    (N : Neighbors K) (i : Fin 3) :
    naturalCliqueType K (automorphismCliqueImage K p f.val (rootCoordinateClique K N i)) =
      rootStabilizerTypeHom K p f (naturalCliqueType K (rootCoordinateClique K N i)) := by
  rw [rootStabilizer_image_coordinate_clique, rootCoordinateClique_type, rootCoordinateClique_type]
  change coordinateTypePermutation (rootStabilizerDirectionHom K p f i) =
    coordinateTypePermutation (rootStabilizerDirectionHom K p f
      (coordinateTypePermutation.symm (coordinateTypePermutation i)))
  rw [coordinateTypePermutation.symm_apply_apply]

theorem rootStabilizer_global_clique_type_formula (f : originalRootStabilizer K p)
    (T : Set (SingularPlanes K 0)) (hT : MaximalClique (originalPlaneAdjacent K) T)
    (hx : originalRootPlane K ∈ T) :
    naturalCliqueType K (automorphismCliqueImage K p f.val T) =
      rootStabilizerTypeHom K p f (naturalCliqueType K T) := by
  obtain ⟨N, i, rfl⟩ := maximal_root_clique_is_coordinate K T hT hx
  exact rootStabilizer_coordinate_type_formula K p f N i

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
