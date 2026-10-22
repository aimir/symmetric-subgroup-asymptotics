import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NaturalCliqueAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NaturalTypeTransport

/-! Actual elementary images compose, and preserve the natural label
of EVERY original maximal clique with a specified original vertex. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexTrialityD4RootedCliques
variable (K : Type) [Field K]

theorem naturalCliqueImage_one (T : Set (SingularPlanes K 0)) : naturalCliqueImage K 1 T = T := by
  unfold naturalCliqueImage
  have he : naturalPlaneImage K 1 = id := funext (naturalPlaneImage_one K)
  rw [he, Set.image_id]

theorem naturalCliqueImage_mul (g h : elementaryRootGroup K 4) (T : Set (SingularPlanes K 0)) :
    naturalCliqueImage K (g * h) T = naturalCliqueImage K g (naturalCliqueImage K h T) := by
  unfold naturalCliqueImage
  rw [Set.image_image]
  congr 1
  funext P
  exact naturalPlaneImage_mul K g h P

theorem naturalCliqueImage_inv_cancel (g : elementaryRootGroup K 4) (T : Set (SingularPlanes K 0)) :
    naturalCliqueImage K g⁻¹ (naturalCliqueImage K g T) = T := by
  rw [← naturalCliqueImage_mul, inv_mul_cancel, naturalCliqueImage_one]

theorem naturalImage_type_of_maximal_clique [Finite K] (h : elementaryRootGroup K 4)
    (T : Set (SingularPlanes K 0)) (hT : MaximalClique (originalPlaneAdjacent K) T)
    (P : SingularPlanes K 0) (hP : P ∈ T) :
    naturalCliqueType K (naturalCliqueImage K h T) = naturalCliqueType K T := by
  obtain ⟨g, hg⟩ := exists_natural_root_transporter K P
  let T0 := naturalCliqueImage K g⁻¹ T
  have hT0 : MaximalClique (originalPlaneAdjacent K) T0 := naturalCliqueImage_maximal K g⁻¹ T hT
  have hr : originalRootPlane K ∈ T0 := by
    refine ⟨P, hP, ?_⟩
    rw [← hg, naturalPlaneImage_inv_cancel]
  have he : T = naturalCliqueImage K g T0 := by
    have hc : naturalCliqueImage K g T0 = T := by
      simpa only [inv_inv] using naturalCliqueImage_inv_cancel K g⁻¹ T
    exact hc.symm
  calc
    naturalCliqueType K (naturalCliqueImage K h T) =
        naturalCliqueType K (naturalCliqueImage K h (naturalCliqueImage K g T0)) :=
      congrArg (fun A => naturalCliqueType K (naturalCliqueImage K h A)) he
    _ = naturalCliqueType K (naturalCliqueImage K (h * g) T0) :=
      congrArg (naturalCliqueType K) (naturalCliqueImage_mul K h g T0).symm
    _ = naturalCliqueType K T0 := naturalImage_type_of_root_maximal_clique K (h * g) T0 hT0 hr
    _ = naturalCliqueType K (naturalCliqueImage K g T0) :=
      (naturalImage_type_of_root_maximal_clique K g T0 hT0 hr).symm
    _ = naturalCliqueType K T := congrArg (naturalCliqueType K) he.symm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
