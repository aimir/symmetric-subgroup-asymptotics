import SymmetricSubgroupAsymptotics.CFSGHermitianLocalFieldCoherence
import SymmetricSubgroupAsymptotics.CFSGHermitianMaximalGallery

/-! A single field component works on all maximal isotropic spaces of
dimension at least three. The common-plane comparisons are propagated
through the proved gallery, not an assumed geometric connectedness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

theorem exists_plane_le_of_two_le_finrank (S : Submodule K (I → K))
    (hS : 2 ≤ Module.finrank K S) :
    ∃ W : Submodule K (I → K), W ≤ S ∧ Module.finrank K W = 2 := by
  have hd : Module.finrank K (Fin 2 → K) ≤ Module.finrank K S := by simpa using hS
  obtain ⟨e, he⟩ := finrank_le_iff_exists_linearMap.mp hd
  let F : (Fin 2 → K) →ₗ[K] (I → K) := S.subtype.comp e
  refine ⟨F.range, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact (e x).property
  · have hF : Function.Injective F := S.subtype_injective.comp he
    have hdF := LinearMap.finrank_range_of_inj hF
    simpa using hdF

theorem semilinearPiece_fields_eq_of_two_le_intersection
    (f : Equiv.Perm (SingularPoint sigma H))
    (S T : IsotropicSpace sigma H) (tau rho : K ≃+* K)
    (F : SemilinearPiece sigma H f S tau) (G : SemilinearPiece sigma H f T rho)
    (hST : 2 ≤ Module.finrank K ↥(S.val ⊓ T.val)) : tau = rho := by
  obtain ⟨W, hW, hdW⟩ := exists_plane_le_of_two_le_finrank (S.val ⊓ T.val) hST
  exact semilinearPiece_fields_eq_of_common_plane sigma H f S T tau rho F G W hdW
    (hW.trans inf_le_left) (hW.trans inf_le_right)

theorem maximal_semilinear_field_component_unique
    (f : Equiv.Perm (SingularPoint sigma H))
    (hswap : ∀ x y, CFSGTwistedAUnitaryParameters.hermitianPair sigma H x y = 0 ↔
      CFSGTwistedAUnitaryParameters.hermitianPair sigma H y x = 0)
    (hmin : ∀ S : MaximalSpace sigma H, 3 ≤ Module.finrank K S.val)
    (tau : MaximalSpace sigma H → K ≃+* K)
    (F : ∀ S : MaximalSpace sigma H,
      SemilinearPiece sigma H f ⟨S.val, S.property.1⟩ (tau S))
    (S T : MaximalSpace sigma H) : tau S = tau T := by
  have hstep : ∀ A B : MaximalSpace sigma H, GalleryStep sigma H A B → tau A = tau B := by
    intro A B hAB
    apply semilinearPiece_fields_eq_of_two_le_intersection sigma H f
      ⟨A.val, A.property.1⟩ ⟨B.val, B.property.1⟩ (tau A) (tau B) (F A) (F B)
    change 2 ≤ Module.finrank K ↥(A.val ⊓ B.val)
    have hA := hmin A
    change Module.finrank K A.val ≤ Module.finrank K ↥(A.val ⊓ B.val) + 1 at hAB
    omega
  have hpath := maximal_gallery_connected sigma H hswap S T
  induction hpath with
  | refl => rfl
  | @tail B C _ hBC ih => exact ih.trans (hstep B C hBC)

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
