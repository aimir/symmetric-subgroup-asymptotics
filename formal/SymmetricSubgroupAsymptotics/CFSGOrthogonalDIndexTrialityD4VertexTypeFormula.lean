import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4VertexNormalization

/-! At EVERY original plane the constructed local permutation
controls the actual global maximal-clique image. All normalizations
are by proved type-preserving projective inner automorphisms. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexTrialityD4RootedCliques
variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]

theorem vertex_clique_type_formula (f : MulAut (elementaryProjective K 4))
    (P : SingularPlanes K 0) (T : Set (SingularPlanes K 0))
    (hT : MaximalClique (originalPlaneAdjacent K) T) (hP : P ∈ T) :
    naturalCliqueType K (automorphismCliqueImage K p f T) =
      vertexTypePermutation K p f P (naturalCliqueType K T) := by
  let g := planeTransporter K P
  let h := planeTransporter K (singularActionHom K p 0 f P)
  let T0 := naturalCliqueImage K g⁻¹ T
  have hT0 : MaximalClique (originalPlaneAdjacent K) T0 := naturalCliqueImage_maximal K g⁻¹ T hT
  have hr : originalRootPlane K ∈ T0 := by
    refine ⟨P, hP, ?_⟩
    have hc := naturalPlaneImage_inv_cancel K g (originalRootPlane K)
    rw [planeTransporter_spec] at hc
    exact hc
  have hcancel : naturalCliqueImage K g T0 = T := by
    simpa only [inv_inv] using naturalCliqueImage_inv_cancel K g⁻¹ T
  have him : automorphismCliqueImage K p (normalizedVertexAutomorphism K p f P) T0 =
      naturalCliqueImage K h⁻¹ (automorphismCliqueImage K p f T) := by
    change automorphismCliqueImage K p
      (elementaryInner K h⁻¹ * f * elementaryInner K g) T0 = _
    rw [automorphismCliqueImage_mul, automorphismCliqueImage_mul,
      elementaryInner_clique_action, elementaryInner_clique_action, hcancel]
  have hroot := rootStabilizer_global_clique_type_formula K p
    (normalizedVertexStabilizer K p f P) T0 hT0 hr
  change naturalCliqueType K (automorphismCliqueImage K p
      (normalizedVertexAutomorphism K p f P) T0) =
    vertexTypePermutation K p f P (naturalCliqueType K T0) at hroot
  rw [him] at hroot
  have hFT := automorphismCliqueImage_maximal K p f T hT
  have hFP : singularActionHom K p 0 f P ∈ automorphismCliqueImage K p f T := ⟨P, hP, rfl⟩
  calc
    naturalCliqueType K (automorphismCliqueImage K p f T) =
        naturalCliqueType K (naturalCliqueImage K h⁻¹ (automorphismCliqueImage K p f T)) :=
      (naturalImage_type_of_maximal_clique K h⁻¹ _ hFT _ hFP).symm
    _ = vertexTypePermutation K p f P (naturalCliqueType K T0) := hroot
    _ = vertexTypePermutation K p f P (naturalCliqueType K T) :=
      congrArg (vertexTypePermutation K p f P) (naturalImage_type_of_maximal_clique K g⁻¹ T hT P hP)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
