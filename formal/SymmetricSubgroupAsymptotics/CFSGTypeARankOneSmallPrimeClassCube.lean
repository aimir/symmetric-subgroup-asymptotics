import SymmetricSubgroupAsymptotics.CFSGTypeARankOneOddClassCube
import SymmetricSubgroupAsymptotics.CFSGPSLTwoThreeModFourPermutationDegree

/-! A single prime-field class budget handles the remaining small
three-modulo-four fields. The index bound is proved from the actual root
action, rather than a table of subgroups or primitive actions. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeARankOneSmallPrimeClassCube
open PrimitiveSocleRawStructure

theorem field_square_le_order (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    q.order^2 ≤ Nat.card (CFSG.Models.A 1 q) := by
  have h : q.order*(q.order-1)*(q.order+1) ≤ 2*Nat.card (CFSG.Models.A 1 q) := by
    simpa only [q.card_field] using
      CFSGPSLTwoGeometry.twice_projective_card_ge_classical_order (F:=q.Field)
  have hlo : 2*q.order^2 ≤ q.order*(q.order-1)*(q.order+1) := by
    have hb := Nat.mul_le_mul (Nat.mul_le_mul_left q.order (show 2 ≤ q.order-1 by omega))
      (Nat.le_succ q.order)
    convert hb using 1 <;> ring
  omega

theorem component_class_cube (q : CFSG.PrimePower) (hprime : q.order.Prime)
    (hlo : 7 ≤ q.order) (hhi : q.order ≤ 11) :
    (Nat.card (ConjClasses (CFSG.Models.A 1 q))*Nat.card (Outer (CFSG.Models.A 1 q)))^3 ≤
      5^(q.order-1) := by
  have he : q.exponent=1 := Nat.Prime.eq_one_of_pow hprime
  have hp : q.prime≠2 := by
    have horder : q.order=q.prime := by simp only [CFSG.PrimePower.order,he,pow_one]
    omega
  have hc : Nat.card (ConjClasses (CFSG.Models.A 1 q)) ≤ 8 := by
    have h := CFSGTypeARankOneOddClassCube.twice_class_card_le q hp
    omega
  have ho : Nat.card (Outer (CFSG.Models.A 1 q)) ≤ 2 := by
    have h := CFSGPSLTwoOuterBound.typeA_rank_one_outer_card q
    omega
  have hb := Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3
  exact hb.trans ((by decide : (8*2)^3 ≤ 5^6).trans
    (Nat.pow_le_pow_right (by decide) (by omega)))

end SymmetricSubgroupAsymptotics.CFSGTypeARankOneSmallPrimeClassCube
