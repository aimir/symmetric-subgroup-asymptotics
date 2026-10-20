import SymmetricSubgroupAsymptotics.ProductBlockFrameGenerators

/-! Exact component coordinates for the kernel of an original physical
block frame. No ambient-group replacement, quotient, or capacity premise
is introduced. For two blocks the pair of coordinates is injective. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.ProductBlockFrame

variable {X I F : Type} {U : Subgroup (Equiv.Perm X)}
    (C : ProductBlockFrame U I F)

private theorem kernel_pair (u : C.top.ker) (i : I) (x : F) :
    C.frame.symm ((u.1 : Equiv.Perm X) (C.frame (i,x))) =
      (i,(C.frame.symm ((u.1 : Equiv.Perm X) (C.frame (i,x)))).2) := by
  apply Prod.ext
  · have h := C.intertwine u.1 (i,x)
    rw [u.2] at h
    exact h
  · rfl

/-- The literal action of an original block-kernel element on one fibre. -/
def kernelCoordinatePerm (i : I) (u : C.top.ker) : Equiv.Perm F where
  toFun x := (C.frame.symm ((u.1 : Equiv.Perm X) (C.frame (i,x)))).2
  invFun x := (C.frame.symm (((u⁻¹).1 : Equiv.Perm X) (C.frame (i,x)))).2
  left_inv x := by
    have hu : ((u.1 : Equiv.Perm X)⁻¹)
        ((u.1 : Equiv.Perm X) (C.frame (i,x))) = C.frame (i,x) :=
      (u.1 : Equiv.Perm X).symm_apply_apply _
    have h := congrArg (fun p : I × F =>
      (C.frame.symm (((u⁻¹).1 : Equiv.Perm X) (C.frame p))).2)
      (C.kernel_pair u i x)
    simpa only [C.frame.apply_symm_apply, Subgroup.coe_inv,
      hu, C.frame.symm_apply_apply] using h.symm
  right_inv x := by
    have hu : (u.1 : Equiv.Perm X)
        (((u.1 : Equiv.Perm X)⁻¹) (C.frame (i,x))) = C.frame (i,x) :=
      (u.1 : Equiv.Perm X).apply_symm_apply _
    have h := congrArg (fun p : I × F =>
      (C.frame.symm ((u.1 : Equiv.Perm X) (C.frame p))).2)
      (C.kernel_pair u⁻¹ i x)
    simpa only [C.frame.apply_symm_apply, Subgroup.coe_inv,
      hu, C.frame.symm_apply_apply] using h.symm

/-- Actual fibre restriction is a homomorphism on the original block kernel. -/
def kernelCoordinate (i : I) : C.top.ker →* Equiv.Perm F where
  toFun := C.kernelCoordinatePerm i
  map_one' := by
    apply Equiv.ext
    intro x
    simp [kernelCoordinatePerm]
  map_mul' u v := by
    apply Equiv.ext
    intro x
    have hp := congrArg C.frame (C.kernel_pair v i x)
    have hv : C.frame (i,(C.kernelCoordinatePerm i v) x) =
        (v.1 : Equiv.Perm X) (C.frame (i,x)) := by
      simpa only [C.frame.apply_symm_apply, kernelCoordinatePerm] using hp.symm
    change (C.frame.symm (((u*v).1 : Equiv.Perm X) (C.frame (i,x)))).2 =
      (C.frame.symm ((u.1 : Equiv.Perm X)
        (C.frame (i,(C.kernelCoordinatePerm i v) x)))).2
    rw [hv]
    rfl

/-- Equality on every physical fibre determines the original permutation. -/
theorem kernelCoordinates_joint_injective :
    Function.Injective (fun u : C.top.ker => fun i : I => C.kernelCoordinate i u) := by
  intro u v h
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  let p := C.frame.symm x
  have hx : x = C.frame p := (C.frame.apply_symm_apply x).symm
  rw [hx]
  apply C.frame.symm.injective
  rw [C.kernel_pair u p.1 p.2, C.kernel_pair v p.1 p.2]
  refine Prod.ext ?_ ?_
  · rfl
  · exact congrArg (fun q : Equiv.Perm F => q p.2) (congrFun h p.1)

/-- The actual two-block kernel embeds in its two component images. -/
theorem twoKernelCoordinates_joint_injective
    {X F : Type} {U : Subgroup (Equiv.Perm X)}
    (C : ProductBlockFrame U (Fin 2) F) :
    Function.Injective (fun u : C.top.ker =>
      (C.kernelCoordinate 0 u,C.kernelCoordinate 1 u)) := by
  intro u v h
  apply C.kernelCoordinates_joint_injective
  funext i
  fin_cases i
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- Concrete pair homomorphism used to form the actual subdirect image. -/
def twoKernelMap
    {X F : Type} {U : Subgroup (Equiv.Perm X)}
    (C : ProductBlockFrame U (Fin 2) F) :
    C.top.ker →* (Equiv.Perm F × Equiv.Perm F) :=
  (C.kernelCoordinate 0).prod (C.kernelCoordinate 1)

theorem twoKernelMap_injective
    {X F : Type} {U : Subgroup (Equiv.Perm X)}
    (C : ProductBlockFrame U (Fin 2) F) :
    Function.Injective C.twoKernelMap := C.twoKernelCoordinates_joint_injective

end SymmetricSubgroupAsymptotics.ProductBlockFrame
