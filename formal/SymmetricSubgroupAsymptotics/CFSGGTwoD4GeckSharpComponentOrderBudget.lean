import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckFixedBruhatOrderUpper
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalOuterBound

/-! The actual fixed Bruhat cover and original outer bound together
give a uniform degree-twenty component ceiling. No proper-index or
group-order formula is supplied as a hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckSharpComponentOrderBudget
open PrimitiveSocleRawStructure

theorem order_mul_outer_le (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    [IsSimpleGroup (CFSG.Models.G2 q)]
    (hn : ¬IsMulCommutative (CFSG.Models.G2 q)) :
    Nat.card (CFSG.Models.G2 q)*Nat.card (Outer (CFSG.Models.G2 q)) ≤ q.order^20 := by
  have hf : q.exponent ≤ q.order := q.exponent.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_left q.prime_isPrime.two_le _)
  have h48 : 48 ≤ q.order^4 := (by decide : 48 ≤ 3^4).trans
    (Nat.pow_le_pow_left hq 4)
  calc
    Nat.card (CFSG.Models.G2 q)*Nat.card (Outer (CFSG.Models.G2 q)) ≤
        (24*q.exponent*q.order^14)*(2*q.exponent) := Nat.mul_le_mul
      (CFSGGTwoD4GeckFixedBruhatOrderUpper.typeGTwo_order_le q hn)
      (CFSGGTwoD4GeckOriginalOuterBound.typeGTwo_outer_card_le_two_exponent q)
    _ = 48*q.exponent^2*q.order^14 := by ring
    _ ≤ 48*q.order^2*q.order^14 := Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hf 2))
    _ ≤ q.order^4*q.order^2*q.order^14 := Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ h48)
    _ = q.order^20 := by ring

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckSharpComponentOrderBudget
