import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4GeneratorSteps
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NeighborAutomorphism
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexIsometryNeighborCount
import Mathlib.Logic.Relation

/-! Actual natural elementary-D4 elements act on the SAME original
singular two-planes and transport genuine adjacency paths. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexResidualNeighborCount CFSGOrthogonalDIndexIsometryNeighborCount
variable (K : Type) [Field K]

def originalPlaneAdjacent (P Q : SingularPlanes K 0) : Prop := QuadraticAdjacent K 4 P.val Q.val

theorem originalPlaneAdjacent_symm {P Q : SingularPlanes K 0}
    (h : originalPlaneAdjacent K P Q) : originalPlaneAdjacent K Q P := by
  refine ⟨Ne.symm h.1, ?_, ?_⟩
  · change Module.finrank K ↥(Q.val ⊓ P.val) = 1
    rw [inf_comm]
    exact h.2.1
  · intro x hx
    exact h.2.2 x (by simpa only [sup_comm] using hx)

def naturalPlaneImage (g : elementaryRootGroup K 4) (P : SingularPlanes K 0) : SingularPlanes K 0 :=
  ⟨P.val.map (naturalLinearHom K 4 g).toLinearMap,
    ((naturalLinearHom K 4 g).finrank_map_eq P.val).trans P.property.1, by
      rintro x ⟨y, hy, rfl⟩
      exact (elementary_preserves_bundledQ K 0 g y).trans (P.property.2 y hy)⟩

theorem naturalPlaneImage_one (P : SingularPlanes K 0) : naturalPlaneImage K 1 P = P := by
  apply Subtype.ext
  change P.val.map (naturalLinearHom K 4 1).toLinearMap = P.val
  rw [map_one]
  exact Submodule.map_id P.val

theorem naturalPlaneImage_mul (g h : elementaryRootGroup K 4) (P : SingularPlanes K 0) :
    naturalPlaneImage K (g * h) P = naturalPlaneImage K g (naturalPlaneImage K h P) := by
  apply Subtype.ext
  change P.val.map (naturalLinearHom K 4 (g * h)).toLinearMap =
    (P.val.map (naturalLinearHom K 4 h).toLinearMap).map (naturalLinearHom K 4 g).toLinearMap
  rw [map_mul, ← Submodule.map_comp]
  rfl

theorem naturalPlaneImage_inv_cancel (g : elementaryRootGroup K 4) (P : SingularPlanes K 0) :
    naturalPlaneImage K g⁻¹ (naturalPlaneImage K g P) = P := by
  rw [← naturalPlaneImage_mul, inv_mul_cancel, naturalPlaneImage_one]

theorem naturalPlaneImage_adjacent (g : elementaryRootGroup K 4) {P Q : SingularPlanes K 0}
    (h : originalPlaneAdjacent K P Q) :
    originalPlaneAdjacent K (naturalPlaneImage K g P) (naturalPlaneImage K g Q) :=
  quadraticAdjacent_map K 4 (naturalLinearHom K 4 g)
    (elementary_preserves_bundledQ K 0 g) P.val Q.val h

theorem naturalPlaneImage_reachable (g : elementaryRootGroup K 4) {P Q : SingularPlanes K 0}
    (h : Relation.ReflTransGen (originalPlaneAdjacent K) P Q) :
    Relation.ReflTransGen (originalPlaneAdjacent K) (naturalPlaneImage K g P) (naturalPlaneImage K g Q) :=
  Relation.ReflTransGen.lift (naturalPlaneImage K g) (fun _ _ => naturalPlaneImage_adjacent K g) h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
