import SymmetricSubgroupAsymptotics.CFSGQuadraticMaximalSingularGallery
import SymmetricSubgroupAsymptotics.CFSGQuadraticPolarSemilinearPiece

/-! The field components of local semilinear pieces on actual maximal
Q-singular spaces agree along the proved maximal gallery. This needs
only dimension at least three, not a split orthogonal model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticMaximalFieldCoherence
open CFSGQuadraticMaximalSingularGallery
open CFSGOrthogonalDIndexQuadraticSubspacePoints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]

theorem exists_plane_le (S : Submodule K V) (hS : 2 ≤ Module.finrank K S) :
    ∃ W : Submodule K V, W ≤ S ∧ Module.finrank K W = 2 := by
  have hd : Module.finrank K (Fin 2 → K) ≤ Module.finrank K S := by simpa using hS
  obtain ⟨e, he⟩ := finrank_le_iff_exists_linearMap.mp hd
  let F : (Fin 2 → K) →ₗ[K] V := S.subtype.comp e
  refine ⟨F.range, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact (e x).property
  · have hF : Function.Injective F := S.subtype_injective.comp he
    simpa using LinearMap.finrank_range_of_inj hF

theorem piece_fields_eq_of_intersection (Q : QuadraticForm K V) (f : Equiv.Perm (Points Q))
    (W Z : Subspaces Q) (sigma tau : K ≃+* K)
    (F : SemilinearPiece Q f W sigma) (G : SemilinearPiece Q f Z tau)
    (hWZ : 2 ≤ Module.finrank K (W.val ⊓ Z.val : Submodule K V)) : sigma = tau := by
  obtain ⟨T, hT, hdT⟩ := exists_plane_le (W.val ⊓ Z.val) hWZ
  exact fields_eq_of_common_plane Q f W Z sigma tau F G T hdT
    (hT.trans inf_le_left) (hT.trans inf_le_right)

theorem maximal_field_component_unique (Q : QuadraticForm K V) (f : Equiv.Perm (Points Q))
    (hmin : ∀ M : MaximalSpaces Q, 3 ≤ Module.finrank K M.val)
    (sigma : MaximalSpaces Q → K ≃+* K)
    (F : ∀ M : MaximalSpaces Q, SemilinearPiece Q f ⟨M.val, M.property.1⟩ (sigma M))
    (S T : MaximalSpaces Q) : sigma S = sigma T := by
  have hstep : ∀ A B : MaximalSpaces Q, GalleryStep Q A B → sigma A = sigma B := by
    intro A B hAB
    apply piece_fields_eq_of_intersection Q f ⟨A.val, A.property.1⟩ ⟨B.val, B.property.1⟩
      (sigma A) (sigma B) (F A) (F B)
    change 2 ≤ Module.finrank K (A.val ⊓ B.val : Submodule K V)
    have hA := hmin A
    change Module.finrank K A.val ≤ Module.finrank K (A.val ⊓ B.val : Submodule K V) + 1 at hAB
    omega
  have hpath := gallery_connected Q S T
  induction hpath with
  | refl => rfl
  | @tail B C _ hBC ih => exact ih.trans (hstep B C hBC)

end SymmetricSubgroupAsymptotics.CFSGQuadraticMaximalFieldCoherence
