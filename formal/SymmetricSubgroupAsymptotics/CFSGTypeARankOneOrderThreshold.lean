import SymmetricSubgroupAsymptotics.CFSGPSLTwoBorelCardinality
import SymmetricSubgroupAsymptotics.External.CFSG.Models.LieFamilies

/-! The literal projective Borel order gives a component-size threshold
already at q=16, independently of the weaker proper-index lower bound. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeARankOneOrderThreshold

theorem order_ge_1024 (q : CFSG.PrimePower) (hq : 16 ≤ q.order) :
    1024 ≤ Nat.card (CFSG.Models.A 1 q) := by
  have h : q.order*(q.order-1)*(q.order+1) ≤ 2*Nat.card (CFSG.Models.A 1 q) := by
    simpa only [q.card_field] using
      CFSGPSLTwoGeometry.twice_projective_card_ge_classical_order (F:=q.Field)
  have hlo := Nat.mul_le_mul
    (Nat.mul_le_mul hq (Nat.sub_le_sub_right hq 1)) (Nat.add_le_add_right hq 1)
  norm_num only [Nat.reduceAdd,Nat.reduceSub,Nat.reduceMul] at hlo
  omega

end SymmetricSubgroupAsymptotics.CFSGTypeARankOneOrderThreshold
