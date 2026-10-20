import SymmetricSubgroupAsymptotics.ProductQuartetFrameAffineCoordinates
import SymmetricSubgroupAsymptotics.ProductBlockFrameKernelCoordinates
import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingKernelPartition

/-! Literal linear-image projection of any physical four-quartet frame.
Its original translation kernel is binary, and each kernel-coordinate
linear part is the actual local matrix in the same image. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)

variable {X : Type} {T : Subgroup (Equiv.Perm X)}
  (C : ProductBlockFrame T (Fin 4) Plane)

def quartetLinearProjection : T →* Frame :=
  SemidirectProduct.rightHom.comp C.affineCoordinates

def quartetLinearImage : Subgroup Frame := C.quartetLinearProjection.range

def quartetLinearMap : T →* C.quartetLinearImage := C.quartetLinearProjection.rangeRestrict

 theorem quartetLinearMap_surjective : Function.Surjective C.quartetLinearMap :=
  C.quartetLinearProjection.rangeRestrict_surjective

@[simp] theorem quartetLinearMap_top (u : T) :
    (C.quartetLinearMap u : Frame).right=C.top u := rfl

 theorem quartetLinearMap_kernel_binary : IsPGroup 2 C.quartetLinearMap.ker := by
  intro u
  refine ⟨1,Subtype.ext ?_⟩
  change u.val^2=1
  apply C.affineCoordinates_injective
  rw [map_pow,map_one]
  let a := C.affineCoordinates u.val
  have ha : a.right=1 := congrArg (fun z : C.quartetLinearImage => (z : Frame)) u.property
  have hform : SemidirectProduct.inl a.left=a := SemidirectProduct.ext rfl ha.symm
  change a^2=1
  rw [←hform,←map_pow]
  have hv : a.left^2=1 := by
    funext i
    simp only [Pi.pow_apply,Pi.one_apply]
    rw [pow_two]
    apply Multiplicative.toAdd.injective
    change (a.left i).toAdd+(a.left i).toAdd=0
    exact binaryVector_add_self (a.left i).toAdd
  rw [hv,map_one]

 theorem quartetLinearMap_local (u : T) (hu : C.top u=1) (i : Fin 4) :
    (C.quartetLinearMap u : Frame).left i=
      BinaryPlanePermutationAffineEquiv.linearPart (C.kernelCoordinate i ⟨u,hu⟩) := by
  apply LinearEquiv.ext
  intro v
  change (C.frame.symm ((u : Equiv.Perm X) (C.frame ((C.top u)⁻¹ i,v)))).2+
    (C.frame.symm ((u : Equiv.Perm X) (C.frame ((C.top u)⁻¹ i,0)))).2=
      (C.frame.symm ((u : Equiv.Perm X) (C.frame (i,v)))).2+
        (C.frame.symm ((u : Equiv.Perm X) (C.frame (i,0)))).2
  rw [hu]
  rfl

end SymmetricSubgroupAsymptotics.ProductBlockFrame
