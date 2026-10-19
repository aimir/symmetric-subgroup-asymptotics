import SymmetricSubgroupAsymptotics.ProductBlockFrameActualTopWreath
import SymmetricSubgroupAsymptotics.ProductQuartetFrameAffineCoordinates

/-! Canonical affine coordinates retain the actual original frame, the
actual top image, and its correlated base image. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame
open BinaryPlanePermutationAffineEquiv BinaryPlanePermutationWreathCoordinates
variable {X I R J : Type} {U : Subgroup (Equiv.Perm X)}
  [Group R] [MulAction R J]
  (C : ProductBlockFrame U I Plane) (e : C.top.range ≃* R) (c : I ≃ J)
  (hc : ∀ b : C.top.range, ∀ i : I, c (b • i)=e b • c i)

def canonicalAffine : U →* Model (R := R) (I := J) :=
  coordinates.comp (C.canonicalWreath e c hc)

theorem canonicalAffine_injective : Function.Injective (C.canonicalAffine e c hc) := by
  intro u v h
  apply C.canonicalWreath_injective e c hc
  have hh := congrArg pointWreath h
  simpa only [canonicalAffine, MonoidHom.comp_apply, pointWreath_coordinates] using hh

@[simp] theorem canonicalAffine_top (u : U) :
    (C.canonicalAffine e c hc u).right.right=e (C.top.rangeRestrict u) := rfl

def canonicalAffinePointChart : Plane × J ≃ X :=
  (Equiv.prodCongr (Equiv.refl Plane) c.symm).trans C.affinePointChart

/-- The resulting model is precisely the original image, not its ambient wreath. -/
def canonicalAffineImageEquiv : U ≃* (C.canonicalAffine e c hc).range :=
  MulEquiv.ofBijective (C.canonicalAffine e c hc).rangeRestrict
    ⟨fun _ _ h => C.canonicalAffine_injective e c hc (congrArg Subtype.val h),
      (C.canonicalAffine e c hc).rangeRestrict_surjective⟩
end SymmetricSubgroupAsymptotics.ProductBlockFrame
