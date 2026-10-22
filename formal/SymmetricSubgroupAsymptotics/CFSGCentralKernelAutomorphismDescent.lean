import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! A GIVEN source automorphism descends along a proved surjection with
kernel equal to the source centre. This does not lift arbitrary target
automorphisms. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCentralKernelAutomorphismDescent
variable {G Q : Type*} [Group G] [Group Q]
    (f : G→*Q) (hsurj : Function.Surjective f) (hker : f.ker=Subgroup.center G)

include hker in
private theorem kernel_map (e : MulAut G) : f.ker.map e.toMonoidHom=f.ker := by
  rw [hker]
  exact Subgroup.characteristic_iff_map_eq.mp (inferInstance : (Subgroup.center G).Characteristic) e

def descend (e : MulAut G) : MulAut Q :=
  ((QuotientGroup.quotientKerEquivOfSurjective f hsurj).symm.trans
    (QuotientGroup.congr f.ker f.ker e (kernel_map f hker e))).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hsurj)

theorem descend_apply (e : MulAut G) (x : G) :
    descend f hsurj hker e (f x)=f (e x) := by
  let q := QuotientGroup.quotientKerEquivOfSurjective f hsurj
  have hq : q (QuotientGroup.mk' f.ker x)=f x := rfl
  rw [←hq]
  change q ((QuotientGroup.congr f.ker f.ker e (kernel_map f hker e))
    (q.symm (q (QuotientGroup.mk' f.ker x))))=f (e x)
  rw [MulEquiv.symm_apply_apply,QuotientGroup.congr_mk']
  rfl

theorem descend_subgroup_image (e : MulAut G) (R : Subgroup G) :
    (R.map f).map (descend f hsurj hker e).toMonoidHom=(R.map e.toMonoidHom).map f := by
  rw [Subgroup.map_map,Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  exact descend_apply f hsurj hker e x

end SymmetricSubgroupAsymptotics.CFSGCentralKernelAutomorphismDescent
