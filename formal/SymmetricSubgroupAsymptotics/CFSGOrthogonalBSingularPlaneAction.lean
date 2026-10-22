import SymmetricSubgroupAsymptotics.CFSGOrthogonalBProjectivePlaneAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularPlaneLabels

/-! Every actual projective B automorphism acts on ALL original totally
singular two-dimensional submodules through the exact root-line label.
This is an action on polar lines; no polar-point reconstruction or
semilinear realization is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent
variable {K : Type} [Field K] [Finite K]

abbrev SingularPlanes (s : ℕ) := {P : Submodule K (Index (s + 3) → K) //
  Module.finrank K P = 2 ∧ IsTotallySingular (K := K) s P}

def singularPlaneEquiv (h2 : (2 : K) ≠ 0) (s : ℕ) :
    SingularPlanes (K := K) s ≃ Planes (K := K) s where
  toFun P := ⟨P.val, (singular_two_plane_iff_conjugateRootPlane h2 s P.val).mp P.property⟩
  invFun P := ⟨P.val, (singular_two_plane_iff_conjugateRootPlane h2 s P.val).mpr P.property⟩
  left_inv P := Subtype.ext rfl
  right_inv P := Subtype.ext rfl

def singularLabel (h2 : (2 : K) ≠ 0) (s : ℕ) (P : SingularPlanes (K := K) s) :
    Subgroup (elementaryProjective K (s + 3)) :=
  projectiveLabel h2 s (singularPlaneEquiv h2 s P)

theorem singularLabel_injective (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) : Function.Injective (singularLabel (K := K) h2 s) :=
  (projectiveLabel_injective p h2 s).comp (singularPlaneEquiv h2 s).injective

theorem singular_stable (p : ℕ) [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0) (s : ℕ)
    (f : MulAut (elementaryProjective K (s + 3))) (P : SingularPlanes (K := K) s) :
    ∃ Q, singularLabel h2 s Q = (singularLabel h2 s P).map f.toMonoidHom := by
  obtain ⟨Q, hQ⟩ := projective_stable p h2 s f (singularPlaneEquiv h2 s P)
  refine ⟨(singularPlaneEquiv h2 s).symm Q, ?_⟩
  change projectiveLabel h2 s ((singularPlaneEquiv h2 s) ((singularPlaneEquiv h2 s).symm Q)) = _
  rw [(singularPlaneEquiv h2 s).apply_symm_apply]
  exact hQ

def singularActionHom (p : ℕ) [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0) (s : ℕ) :
    MulAut (elementaryProjective K (s + 3)) →* Equiv.Perm (SingularPlanes (K := K) s) :=
  CFSGSubgroupFamilyAction.permutationHom (MonoidHom.id _) (singularLabel h2 s)
    (singularLabel_injective p h2 s) (singular_stable p h2 s)

theorem singularLabel_action (p : ℕ) [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0) (s : ℕ)
    (f : MulAut (elementaryProjective K (s + 3))) (P : SingularPlanes (K := K) s) :
    singularLabel h2 s (singularActionHom p h2 s f P) =
      (singularLabel h2 s P).map f.toMonoidHom :=
  CFSGSubgroupFamilyAction.label_permutation (MonoidHom.id _) (singularLabel h2 s)
    (singularLabel_injective p h2 s) (singular_stable p h2 s) f P

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
