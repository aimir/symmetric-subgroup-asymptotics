import SymmetricSubgroupAsymptotics.ProjectiveSLThreeQuaternaryClassBound
import SymmetricSubgroupAsymptotics.CFSGTypeAOuterGcdCardinality
import SymmetricSubgroupAsymptotics.CFSGTypeAProperIndexOrderBudget
import Mathlib.Data.Nat.Prime.Int

/-! The proved SL3 central-scalar class argument gives ten classes on
this SAME original projective model. Its actual outer ceiling twelve
and proper-index lower bound sixteen pay the24-reserve packet without
supplying a class number or identifying another group or action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeARankTwoQuaternaryClassPacket
open PrimitiveSocleRawStructure

private theorem prime_exponent (q : CFSG.PrimePower) (hq : q.order=4) :
    q.prime=2 ∧ q.exponent=2 :=
  Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 2) q.exponent_pos.ne'
    (by decide : (2:ℕ)≠0) (show q.prime^q.exponent=2^2 from hq)

theorem class_card_le_ten (q : CFSG.PrimePower) (hq : q.order=4) :
    Nat.card (ConjClasses (CFSG.Models.A 2 q)) ≤ 10 := by
  have hp := (prime_exponent q hq).1
  letI : CharP q.Field 2 := by rw [←hp]; infer_instance
  exact ProjectiveSLThreeQuaternaryClassBound.class_card_le_ten (q.card_field.trans hq)

theorem component_class_card_le_oneTwenty (q : CFSG.PrimePower) (hq : q.order=4)
    [IsSimpleGroup (CFSG.Models.A 2 q)] :
    Nat.card (ConjClasses (CFSG.Models.A 2 q))*
      Nat.card (Outer (CFSG.Models.A 2 q)) ≤ 120 := by
  have hf := (prime_exponent q hq).2
  have ho : Nat.card (Outer (CFSG.Models.A 2 q)) ≤ 12 := by
    simpa only [hq,hf] using
      CFSGTypeAOuterGcdCardinality.typeA_higher_outer_card_le_gcd 2 (by decide) q
  exact (Nat.mul_le_mul (class_card_le_ten q hq) ho).trans_eq (by decide : 10*12=120)

theorem scaled_class_cube_le_proper_index (q : CFSG.PrimePower) (hq : q.order=4)
    [IsSimpleGroup (CFSG.Models.A 2 q)]
    (H : Subgroup (CFSG.Models.A 2 q)) (hH : H≠⊤) :
    24*(Nat.card (ConjClasses (CFSG.Models.A 2 q))*
      Nat.card (Outer (CFSG.Models.A 2 q)))^3 ≤ 3^H.index := by
  have hi : 16≤H.index := by
    simpa only [hq] using
      CFSGTypeAProperIndexOrderBudget.typeA_higher_field_power_le_proper_index 2 (by decide) q H hH
  exact ((Nat.mul_le_mul_left 24 (Nat.pow_le_pow_left
      (component_class_card_le_oneTwenty q hq) 3)).trans
    (by decide +kernel : 24*120^3≤3^16)).trans
      (Nat.pow_le_pow_right (by decide) hi)

end SymmetricSubgroupAsymptotics.CFSGTypeARankTwoQuaternaryClassPacket
