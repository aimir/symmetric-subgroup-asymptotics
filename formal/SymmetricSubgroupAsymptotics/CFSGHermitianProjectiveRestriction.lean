import SymmetricSubgroupAsymptotics.CFSGHermitianIsotropicJoinIncidence
import SymmetricSubgroupAsymptotics.CFSGPolarSubspaceSemilinearRestriction

/-! Exact projective restrictions of the literal Hermitian point map.
The already proved projective-frame theorem applies on spaces of
dimension at least three, after line incidence has been proved. This
does not assert a semilinear extension to the whole unitary space. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

def projectiveInside (S : IsotropicSpace sigma H) : ℙ K S.val ≃ PointsInside sigma H S :=
  (Projectivization.equivSubmodule K S.val).trans (pointsInsideEquiv sigma H S).symm

theorem projectiveInside_submodule (S : IsotropicSpace sigma H) (p : ℙ K S.val) :
    (projectiveInside sigma H S p).val.val = p.submodule.map S.val.subtype := rfl

theorem projectiveInside_line (S : IsotropicSpace sigma H) (p q r : ℙ K S.val) :
    (projectiveInside sigma H S p).val.val ≤
      (projectiveInside sigma H S q).val.val ⊔ (projectiveInside sigma H S r).val.val ↔
        p.submodule ≤ q.submodule ⊔ r.submodule := by
  rw [projectiveInside_submodule, projectiveInside_submodule, projectiveInside_submodule, ← Submodule.map_sup]
  exact Submodule.map_le_map_iff_of_injective S.val.subtype_injective _ _

variable (hsep : ∀ S : IsotropicSpace sigma H, SeparatedByMaximal sigma H S.val)
variable (f : Equiv.Perm (SingularPoint sigma H)) (hf : PreservesOrthogonality sigma H f)

def projectiveRestriction (S : IsotropicSpace sigma H) :
    ℙ K S.val ≃ ℙ K (isotropicSpaceImage sigma H f hf S).val :=
  (projectiveInside sigma H S).trans ((isotropicImagePointsEquiv sigma H hsep f hf S).trans
    (projectiveInside sigma H (isotropicSpaceImage sigma H f hf S)).symm)

theorem projectiveRestriction_point (S : IsotropicSpace sigma H) (p : ℙ K S.val) :
    (projectiveInside sigma H (isotropicSpaceImage sigma H f hf S)
      (projectiveRestriction sigma H hsep f hf S p)).val = f (projectiveInside sigma H S p).val := by
  simp only [projectiveRestriction, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

theorem projectiveRestriction_line [Finite K] (S : IsotropicSpace sigma H) (p q r : ℙ K S.val) :
    (projectiveRestriction sigma H hsep f hf S p).submodule ≤
      (projectiveRestriction sigma H hsep f hf S q).submodule ⊔
      (projectiveRestriction sigma H hsep f hf S r).submodule ↔
        p.submodule ≤ q.submodule ⊔ r.submodule := by
  rw [← projectiveInside_line sigma H (isotropicSpaceImage sigma H f hf S),
    projectiveRestriction_point, projectiveRestriction_point, projectiveRestriction_point]
  exact (isotropicSpaceImage_point_join_incidence sigma H hsep f hf S
    (projectiveInside sigma H S q).val (projectiveInside sigma H S r).val
    (projectiveInside sigma H S p).val
    (projectiveInside sigma H S q).property (projectiveInside sigma H S r).property).trans
      (projectiveInside_line sigma H S p q r)

open CFSGPolarSubspacePoints in
def coordinateRestriction [Finite K] (S : IsotropicSpace sigma H) (d : ℕ)
    (e : S.val ≃ₗ[K] (Fin d → K))
    (e' : (isotropicSpaceImage sigma H f hf S).val ≃ₗ[K] (Fin d → K)) :
    CFSGProjectiveFrameCoordinates.collineationGroup (F := K) (n := Fin d) :=
  ⟨(linearProjectiveEquiv e.symm).trans ((projectiveRestriction sigma H hsep f hf S).trans
    (linearProjectiveEquiv e')), by
    intro p q r
    change (linearProjectiveEquiv e' (projectiveRestriction sigma H hsep f hf S
      (linearProjectiveEquiv e.symm p))).submodule ≤ _ ↔ _
    exact (linearProjectiveEquiv_line e' _ _ _).trans
      ((projectiveRestriction_line sigma H hsep f hf S _ _ _).trans
        (linearProjectiveEquiv_line e.symm p q r))⟩

theorem exists_coordinate_semilinear [Finite K] (S : IsotropicSpace sigma H) (d : ℕ)
    (e : S.val ≃ₗ[K] (Fin (d + 3) → K))
    (e' : (isotropicSpaceImage sigma H f hf S).val ≃ₗ[K] (Fin (d + 3) → K)) :
    ∃ (a : (Fin (d + 3) → K) ≃ₗ[K] (Fin (d + 3) → K)) (tau : K ≃+* K),
      ∀ p, (coordinateRestriction sigma H hsep f hf S (d + 3) e e').val p =
        CFSGProjectiveFrameCoordinates.linearPointEquiv a (CFSGProjectiveFieldAction.pointEquiv tau p) := by
  exact CFSGProjectiveSemilinearDecomposition.exists_decomposition
    (coordinateRestriction sigma H hsep f hf S (d + 3) e e')
    ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
