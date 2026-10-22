import SymmetricSubgroupAsymptotics.CFSGOrthogonalBNaturalPointCompatibility
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularSubspaceDimension
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBMaximalSubspaceOrbit

/-! The reconstructed subspace action of an inner automorphism is its
literal natural matrix map. Hence a maximal singular image of any actual
group automorphism can be aligned by an actual inner automorphism. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBSingularVectorCount CFSGPolarSubspacePoints
variable {K : Type} [Field K] [Finite K]

theorem singularSubspaceAction_inner_map (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (g : elementaryRootGroup K (s+3))
    (W : Subspaces (gram K (s+3)).toBilin') :
    (singularSubspaceAction p h2 s (MulAut.conj (naturalProjection s g)) W).val=
      W.val.map (Matrix.mulVecLin (g.val : Mat K (s+3))) := by
  apply Submodule.eq_of_le_of_finrank_le
  · rintro x (rfl|⟨P,hP,hx⟩)
    · exact Submodule.zero_mem _
    · change x∈((originalPointAction p h2 s (MulAut.conj (naturalProjection s g))).val P).val at hx
      rw [originalPointAction_inner] at hx
      exact (Submodule.map_mono hP) hx
  · have hd := (naturalLinearEquiv K (s+3) g).finrank_map_eq W.val
    change Module.finrank K (W.val.map (Matrix.mulVecLin (g.val : Mat K (s+3))))=
      Module.finrank K W.val at hd
    rw [hd,singularSubspaceAction_finrank]

theorem exists_inner_align_full_rank (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (f : MulAut (elementaryProjective K (s+3)))
    (W : Subspaces (gram K (s+3)).toBilin') (hW : Module.finrank K W.val=s+3) :
    ∃g : elementaryRootGroup K (s+3),
      singularSubspaceAction p h2 s ((MulAut.conj (naturalProjection s g))*f) W=
        standardSingularSubspace (s+3) := by
  let W' := singularSubspaceAction p h2 s f W
  have hd : Module.finrank K W'.val=s+3 := (singularSubspaceAction_finrank p h2 s f W).trans hW
  obtain ⟨g,hg⟩ := CFSGOrthogonalBMaximalSubspaceOrbit.exists_normalize_full_rank K h2 (s+3) W' hd
  refine ⟨g,Subtype.ext ?_⟩
  rw [map_mul,Equiv.Perm.mul_apply]
  exact (singularSubspaceAction_inner_map p h2 s g W').trans hg

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
