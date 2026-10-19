import SymmetricSubgroupAsymptotics.Row220OriginalBlockFrame

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row220OriginalBlockFrame

def fibreTransport : Equiv.Perm (Fin 6) where
  toFun := ![5,0,4,3,2,1]
  invFun := ![1,5,4,3,2,0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem swap_zero : ∀ x : Fin 6,
    (originalGenerator 3 : Equiv.Perm (Fin 12)) (pointFrame (0,x)) =
      pointFrame (1,fibreTransport x) := by decide +kernel
private theorem swap_one_inverse : ∀ x : Fin 6,
    ((originalGenerator 3)⁻¹ : Equiv.Perm (Fin 12)) (pointFrame (1,x)) =
      pointFrame (0,fibreTransport.symm x) := by decide +kernel

private theorem kernel_action (k : blockFrame.top.ker) (i : Fin 2) (x : Fin 6) :
    ((k.1 : Original) : Equiv.Perm (Fin 12)) (pointFrame (i,x)) =
      pointFrame (i,blockFrame.kernelCoordinate i k x) := by
  apply pointFrame.symm.injective
  rw [pointFrame.symm_apply_apply]
  apply Prod.ext
  · have h := blockFrame.intertwine k.1 (i,x)
    rw [k.2] at h
    exact h
  · rfl

def conjugatedKernel (k : blockFrame.top.ker) : blockFrame.top.ker :=
  ⟨originalGenerator 3 * k.1 * (originalGenerator 3)⁻¹,by
    change blockFrame.top (originalGenerator 3 * k.1 * (originalGenerator 3)⁻¹) = 1
    rw [map_mul,map_mul,map_inv,k.2,mul_one,mul_inv_cancel]⟩

private theorem conjugated_coordinate (k : blockFrame.top.ker) (x : Fin 6) :
    blockFrame.kernelCoordinate 1 (conjugatedKernel k) x =
      fibreTransport (blockFrame.kernelCoordinate 0 k (fibreTransport.symm x)) := by
  change (pointFrame.symm ((originalGenerator 3 : Equiv.Perm (Fin 12))
    (((k.1 : Original) : Equiv.Perm (Fin 12))
      (((originalGenerator 3)⁻¹ : Equiv.Perm (Fin 12)) (pointFrame (1,x)))))).2 = _
  rw [swap_one_inverse,kernel_action,swap_zero,pointFrame.symm_apply_apply]

theorem component_one_two_pretransitive :
    MulAction.IsMultiplyPretransitive (Component 1) (Fin 6) 2 := by
  apply MulAction.is_two_pretransitive_iff.mpr
  intro a b c d hab hcd
  obtain ⟨g,hg0,hg1⟩ := MulAction.is_two_pretransitive_iff.mp
    component_zero_two_pretransitive
    (show fibreTransport.symm a ≠ fibreTransport.symm b from fun h => hab (fibreTransport.symm.injective h))
    (show fibreTransport.symm c ≠ fibreTransport.symm d from fun h => hcd (fibreTransport.symm.injective h))
  obtain ⟨k,hk⟩ := g.2
  refine ⟨(blockFrame.kernelCoordinate 1).rangeRestrict (conjugatedKernel k),?_,?_⟩
  · change blockFrame.kernelCoordinate 1 (conjugatedKernel k) a = c
    rw [conjugated_coordinate,hk]
    exact (congrArg fibreTransport hg0).trans (fibreTransport.apply_symm_apply c)
  · change blockFrame.kernelCoordinate 1 (conjugatedKernel k) b = d
    rw [conjugated_coordinate,hk]
    exact (congrArg fibreTransport hg1).trans (fibreTransport.apply_symm_apply d)

instance component_primitive (s : Fin 2) : MulAction.IsPreprimitive (Component s) (Fin 6) := by
  fin_cases s
  · exact MulAction.isPreprimitive_of_is_two_pretransitive component_zero_two_pretransitive
  · exact MulAction.isPreprimitive_of_is_two_pretransitive component_one_two_pretransitive

end SymmetricSubgroupAsymptotics.Row220OriginalBlockFrame
