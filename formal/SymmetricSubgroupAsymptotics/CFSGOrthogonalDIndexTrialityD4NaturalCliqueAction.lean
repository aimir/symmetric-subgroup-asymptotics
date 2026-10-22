import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NaturalCliqueTypes
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4PlaneConnectivity

/-! Literal elementary D4 transport acts reversibly on original
planes and their global maximal cliques. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexTrialityD4RootedCliques
open CFSGOrthogonalDIndexSingularPlaneOrbit
variable (K : Type) [Field K]

def naturalPlaneEquiv (g : elementaryRootGroup K 4) : Equiv.Perm (SingularPlanes K 0) where
  toFun := naturalPlaneImage K g
  invFun := naturalPlaneImage K g⁻¹
  left_inv := naturalPlaneImage_inv_cancel K g
  right_inv P := by simpa only [inv_inv] using naturalPlaneImage_inv_cancel K g⁻¹ P

theorem naturalPlaneImage_adjacent_iff (g : elementaryRootGroup K 4)
    (P Q : SingularPlanes K 0) :
    originalPlaneAdjacent K (naturalPlaneImage K g P) (naturalPlaneImage K g Q) ↔
      originalPlaneAdjacent K P Q := by
  constructor
  · intro h
    have hh := naturalPlaneImage_adjacent K g⁻¹ h
    rw [naturalPlaneImage_inv_cancel, naturalPlaneImage_inv_cancel] at hh
    exact hh
  · exact naturalPlaneImage_adjacent K g

theorem naturalCliqueImage_eq_symm_preimage (g : elementaryRootGroup K 4)
    (T : Set (SingularPlanes K 0)) :
    naturalCliqueImage K g T = (naturalPlaneEquiv K g).symm ⁻¹' T := by
  ext P
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    change naturalPlaneImage K g⁻¹ (naturalPlaneImage K g Q) ∈ T
    rw [naturalPlaneImage_inv_cancel]
    exact hQ
  · intro h
    exact ⟨(naturalPlaneEquiv K g).symm P, h, (naturalPlaneEquiv K g).apply_symm_apply P⟩

theorem naturalCliqueImage_maximal (g : elementaryRootGroup K 4)
    (T : Set (SingularPlanes K 0)) (hT : MaximalClique (originalPlaneAdjacent K) T) :
    MaximalClique (originalPlaneAdjacent K) (naturalCliqueImage K g T) := by
  rw [naturalCliqueImage_eq_symm_preimage]
  exact (maximal_clique_preimage_iff (originalPlaneAdjacent K) (originalPlaneAdjacent K)
    (naturalPlaneEquiv K g).symm (fun P Q => naturalPlaneImage_adjacent_iff K g⁻¹ P Q) T).mpr hT

theorem exists_natural_root_transporter (P : SingularPlanes K 0) :
    ∃ g : elementaryRootGroup K 4, naturalPlaneImage K g (originalRootPlane K) = P := by
  obtain ⟨g, hg⟩ := exists_conjugateRootPlane_of_singular K 0 P.val P.property.1 P.property.2
  exact ⟨g, Subtype.ext ((naturalPlaneImage_root_eq_conjugate K g).trans hg.symm)⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
