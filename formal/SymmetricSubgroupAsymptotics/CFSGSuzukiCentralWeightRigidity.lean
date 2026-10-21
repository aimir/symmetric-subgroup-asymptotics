import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentCommutator
import Mathlib.Tactic.Ring

/-! The central Suzuki weight is not additive. Thus an additive shear
intertwining first and central torus weights must vanish. This uses the
actual theta map on the original field, including its positive guard. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical CharTwo
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
open CFSGSuzukiFieldParameters

theorem additive_thetaProduct_weight_eq_zero (m : ℕ) (hm : 1≤m)
    (d : Field m→+Field m)
    (hd : ∀ x : Field m,d x=thetaProduct m x*d 1) : d=0 := by
  obtain ⟨t,ht⟩ := exists_twist_difference_ne_zero m hm
  have he : ((1+t)*(1+theta m t))*d 1=d 1+(t*theta m t)*d 1 := by
    calc
      ((1+t)*(1+theta m t))*d 1=thetaProduct m (1+t)*d 1 := by
        rw [thetaProduct,map_add,map_one (theta m)]
      _=d (1+t) := (hd (1+t)).symm
      _=d 1+d t := map_add d 1 t
      _=d 1+(t*theta m t)*d 1 := by rw [hd t,thetaProduct]
  have hz : d 1*(theta m t+t)=0 := by
    calc
      d 1*(theta m t+t)=((1+t)*(1+theta m t))*d 1+
          (d 1+(t*theta m t)*d 1) := by ring_nf <;> simp
      _=(d 1+(t*theta m t)*d 1)+(d 1+(t*theta m t)*d 1) := by rw [he]
      _=0 := CharTwo.add_self_eq_zero _
  have hd1 : d 1=0 := (mul_eq_zero.mp hz).resolve_right ht
  ext x
  change d x=0
  rw [hd x,hd1,mul_zero]

end SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
