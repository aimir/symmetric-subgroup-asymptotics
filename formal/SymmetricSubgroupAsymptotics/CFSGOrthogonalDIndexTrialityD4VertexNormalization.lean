import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4AutomorphismCliqueAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4RootStabilizerTypeAction

/-! Every original automorphism at every original plane is normalized
by ACTUAL projective inner automorphisms into the proved root stabilizer.
The resulting local natural-type permutation is constructed internally. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
variable (K : Type) [Field K]

def planeTransporter (P : SingularPlanes K 0) : elementaryRootGroup K 4 :=
  Classical.choose (exists_natural_root_transporter K P)

theorem planeTransporter_spec (P : SingularPlanes K 0) :
    naturalPlaneImage K (planeTransporter K P) (originalRootPlane K) = P :=
  Classical.choose_spec (exists_natural_root_transporter K P)

variable [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]

def normalizedVertexAutomorphism (f : MulAut (elementaryProjective K 4))
    (P : SingularPlanes K 0) : MulAut (elementaryProjective K 4) :=
  elementaryInner K ((planeTransporter K (singularActionHom K p 0 f P))⁻¹) * f *
    elementaryInner K (planeTransporter K P)

theorem normalizedVertexAutomorphism_fix (f : MulAut (elementaryProjective K 4))
    (P : SingularPlanes K 0) :
    singularActionHom K p 0 (normalizedVertexAutomorphism K p f P) (originalRootPlane K) =
      originalRootPlane K := by
  unfold normalizedVertexAutomorphism
  rw [map_mul, map_mul]
  change singularActionHom K p 0
    (elementaryInner K ((planeTransporter K (singularActionHom K p 0 f P))⁻¹))
      (singularActionHom K p 0 f
        (singularActionHom K p 0 (elementaryInner K (planeTransporter K P)) (originalRootPlane K))) = _
  simp only [elementaryInner_plane_action]
  rw [planeTransporter_spec]
  have hc := naturalPlaneImage_inv_cancel K
    (planeTransporter K (singularActionHom K p 0 f P)) (originalRootPlane K)
  rw [planeTransporter_spec] at hc
  exact hc

def normalizedVertexStabilizer (f : MulAut (elementaryProjective K 4))
    (P : SingularPlanes K 0) : originalRootStabilizer K p :=
  ⟨normalizedVertexAutomorphism K p f P, normalizedVertexAutomorphism_fix K p f P⟩

def vertexTypePermutation (f : MulAut (elementaryProjective K 4))
    (P : SingularPlanes K 0) : Equiv.Perm (Fin 3) :=
  rootStabilizerTypeHom K p (normalizedVertexStabilizer K p f P)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
