import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGlobalField
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularSubspaceAction

/-! The SAME actual original projective B automorphism has a unique
global field component on every maximal singular space. All incidence,
orthogonality and field coherence are discharged internally. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGlobalField
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace
open CFSGOrthogonalBPlaneFamilyAction CFSGPolarSubspacePoints
variable (K : Type) [Field K] [Finite K]

theorem original_exists_unique_global_field (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (F : MulAut (elementaryProjective K (s+3))) :
    ∃!σ : K≃+*K,∀W : Subspaces (gram K (s+3)).toBilin',
      Module.finrank K W.val=s+3 →
        Nonempty (SemilinearPiece (gram K (s+3)).toBilin'
          (originalPointAction p h2 s F).val W σ) := by
  let B := (gram K (s+3)).toBilin'
  let f := (originalPointAction p h2 s F).val
  obtain ⟨σ,hσ⟩ := exists_global_field K h2 s f (singularActionHom p h2 s F)
    (originalPointAction_incidence p h2 s F) (originalPointAction_preserves_orthogonal p h2 s F)
  refine ⟨σ,hσ,?_⟩
  intro τ hτ
  let P : Subspaces B := ⟨positiveSubspace K (s+3),positiveSubspace_singular K (s+3)⟩
  have hd : Module.finrank K P.val=s+3 := positiveSubspace_finrank K (s+3)
  have hlo : 2≤Module.finrank K (P.val⊓P.val : Submodule K (Index (s+3)→K)) := by
    rw [inf_idem,hd]
    omega
  obtain ⟨T,hT,hTW,hTZ⟩ := exists_common_plane P.val P.val hlo
  exact fields_eq_of_common_plane B f P P τ σ
    (Classical.choice (hτ P hd)) (Classical.choice (hσ P hd)) T hT hTW hTZ

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGlobalField
