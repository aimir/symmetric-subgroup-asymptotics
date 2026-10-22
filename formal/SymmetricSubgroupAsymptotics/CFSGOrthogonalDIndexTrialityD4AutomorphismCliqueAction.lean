import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4InnerCompatibility

/-! The original automorphism action acts reversibly on original
global maximal cliques, with the actual adjacency-preservation proof. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexTrialityD4RootedCliques
variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]

theorem automorphismCliqueImage_one (T : Set (SingularPlanes K 0)) :
    automorphismCliqueImage K p 1 T = T := by
  unfold automorphismCliqueImage
  rw [map_one]
  exact Set.image_id T

theorem automorphismCliqueImage_mul (f g : MulAut (elementaryProjective K 4))
    (T : Set (SingularPlanes K 0)) :
    automorphismCliqueImage K p (f * g) T =
      automorphismCliqueImage K p f (automorphismCliqueImage K p g T) := by
  unfold automorphismCliqueImage
  rw [map_mul, Set.image_image]
  rfl

theorem automorphismCliqueImage_inv_cancel (f : MulAut (elementaryProjective K 4))
    (T : Set (SingularPlanes K 0)) :
    automorphismCliqueImage K p f⁻¹ (automorphismCliqueImage K p f T) = T := by
  rw [← automorphismCliqueImage_mul, inv_mul_cancel, automorphismCliqueImage_one]

theorem automorphismCliqueImage_maximal (f : MulAut (elementaryProjective K 4))
    (T : Set (SingularPlanes K 0)) (hT : MaximalClique (originalPlaneAdjacent K) T) :
    MaximalClique (originalPlaneAdjacent K) (automorphismCliqueImage K p f T) := by
  let e := singularActionHom K p 0 f
  have hset : automorphismCliqueImage K p f T = e.symm ⁻¹' T := by
    ext P
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      change e.symm (e Q) ∈ T
      rw [e.symm_apply_apply]
      exact hQ
    · intro h
      exact ⟨e.symm P, h, e.apply_symm_apply P⟩
  rw [hset]
  apply (maximal_clique_preimage_iff (originalPlaneAdjacent K) (originalPlaneAdjacent K)
    e.symm ?_ T).mpr hT
  intro P Q
  have hh := singularAction_preserves_adjacency K p 0 f⁻¹ P Q
  rw [map_inv] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
