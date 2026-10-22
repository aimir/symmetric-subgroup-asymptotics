import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NaturalCliqueComposition
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4RootCompletionAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneActionFaithful

/-! The original projective inner automorphism action is exactly the
literal natural elementary action on the SAME quadratic plane carrier. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexProjectiveUnipotent CFSGOrthogonalDIndexTrialityD4RootedCliques
variable (K : Type) [Field K]

theorem natural_root_eq_singularPlane (g : elementaryRootGroup K 4) :
    naturalPlaneImage K g (originalRootPlane K) = singularPlane K 0 g :=
  Subtype.ext (naturalPlaneImage_root_eq_conjugate K g)

variable [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]

def elementaryInner (g : elementaryRootGroup K 4) : MulAut (elementaryProjective K 4) :=
  MulAut.conj (projection K 0 g)

theorem elementaryInner_plane_action (g : elementaryRootGroup K 4) (P : SingularPlanes K 0) :
    singularActionHom K p 0 (elementaryInner K g) P = naturalPlaneImage K g P := by
  obtain ⟨h, hh⟩ := exists_natural_root_transporter K P
  rw [← hh]
  calc
    singularActionHom K p 0 (elementaryInner K g) (naturalPlaneImage K h (originalRootPlane K)) =
        singularActionHom K p 0 (elementaryInner K g) (singularPlane K 0 h) :=
      congrArg (singularActionHom K p 0 (elementaryInner K g)) (natural_root_eq_singularPlane K h)
    _ = singularPlane K 0 (g * h) := singularAction_inner_plane K p 0 g h
    _ = naturalPlaneImage K (g * h) (originalRootPlane K) := (natural_root_eq_singularPlane K (g * h)).symm
    _ = naturalPlaneImage K g (naturalPlaneImage K h (originalRootPlane K)) :=
      naturalPlaneImage_mul K g h (originalRootPlane K)

theorem elementaryInner_clique_action (g : elementaryRootGroup K 4) (T : Set (SingularPlanes K 0)) :
    automorphismCliqueImage K p (elementaryInner K g) T = naturalCliqueImage K g T := by
  unfold automorphismCliqueImage naturalCliqueImage
  congr 1
  funext P
  exact elementaryInner_plane_action K p g P

theorem elementaryInner_preserves_clique_type (g : elementaryRootGroup K 4)
    (T : Set (SingularPlanes K 0)) (hT : MaximalClique (originalPlaneAdjacent K) T)
    (P : SingularPlanes K 0) (hP : P ∈ T) :
    naturalCliqueType K (automorphismCliqueImage K p (elementaryInner K g) T) = naturalCliqueType K T := by
  rw [elementaryInner_clique_action]
  exact naturalImage_type_of_maximal_clique K g T hT P hP

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
