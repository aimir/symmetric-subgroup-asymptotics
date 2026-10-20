import SymmetricSubgroupAsymptotics.ProductBlockFrameWreathEmbedding
import SymmetricSubgroupAsymptotics.BinaryPlanePermutationWreathCoordinates

/-! Every actual product frame with four-point plane fibres has faithful
binary affine wreath coordinates. This binds the original action and does
not require a full wreath image. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame
open BinaryPlanePermutationAffineEquiv BinaryPlanePermutationWreathCoordinates
variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
  (C : ProductBlockFrame U I Plane)

/-- The original subgroup, with all correlations among its local maps retained. -/
def affineCoordinates : U →* Model (R := Equiv.Perm I) (I := I) :=
  coordinates.comp C.wreathEmbedding

theorem affineCoordinates_injective : Function.Injective C.affineCoordinates := by
  intro u v h
  apply C.wreathEmbedding_injective
  have hh := congrArg pointWreath h
  simpa only [affineCoordinates, MonoidHom.comp_apply, pointWreath_coordinates] using hh

@[simp] theorem affineCoordinates_top (u : U) :
    (C.affineCoordinates u).right.right = C.top u := rfl

/-- The physical chart has the fibre first, as in the affine point action. -/
def affinePointChart : Plane × I ≃ X := (Equiv.prodComm Plane I).trans C.frame

theorem affineCoordinates_action (u : U) (p : Plane × I) :
    C.affinePointChart (pointAction (C.affineCoordinates u) p) =
      (u : Equiv.Perm X) (C.affinePointChart p) := by
  rw [affineCoordinates, MonoidHom.comp_apply, pointAction_coordinates]
  rcases p with ⟨x,i⟩
  apply C.frame.symm.injective
  simp only [affinePointChart, Equiv.trans_apply, Equiv.prodComm_apply,
    C.frame.symm_apply_apply]
  change ((C.top u) i,
      (C.frame.symm ((u : Equiv.Perm X)
        (C.frame ((C.top u)⁻¹ ((C.top u) i),x)))).2) =
    C.frame.symm ((u : Equiv.Perm X) (C.frame (i,x)))
  rw [Equiv.Perm.inv_def, (C.top u).symm_apply_apply]
  apply Prod.ext
  · exact (C.intertwine u (i,x)).symm
  · rfl

/-- The image is the actual correlated affine subgroup, with exact original map. -/
def affineImageEquiv : U ≃* C.affineCoordinates.range :=
  MulEquiv.ofBijective C.affineCoordinates.rangeRestrict
    ⟨fun _ _ h => C.affineCoordinates_injective (congrArg Subtype.val h),
      C.affineCoordinates.rangeRestrict_surjective⟩
end SymmetricSubgroupAsymptotics.ProductBlockFrame
