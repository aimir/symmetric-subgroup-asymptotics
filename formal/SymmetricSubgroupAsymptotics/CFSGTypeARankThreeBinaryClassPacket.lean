import SymmetricSubgroupAsymptotics.BinaryFourProjectivePrimaryClassBound
import SymmetricSubgroupAsymptotics.CFSGTypeARankThreeCardTwo
import SymmetricSubgroupAsymptotics.CFSGTypeAOuterGcdCardinality
import SymmetricSubgroupAsymptotics.CFSGTypeAProperIndexOrderBudget
import Mathlib.Data.Nat.Prime.Int

/-! Literal PSL4 over a two-element field has at most fourteen classes,
outer ceiling two, and proper index at least eight. The scaled24 packet
is asserted only for an ACTUAL proper index at least twelve. The lower
indices are retained, not discarded or relabelled as natural actions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeARankThreeBinaryClassPacket
open PrimitiveSocleRawStructure

private theorem prime_exponent (q : CFSG.PrimePower) (hq : q.order=2) :
    q.prime=2 ∧ q.exponent=1 :=
  Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 2) q.exponent_pos.ne'
    (by decide : (1:ℕ)≠0) (show q.prime^q.exponent=2^1 from hq)

theorem class_card_le_fourteen (q : CFSG.PrimePower) (hq : q.order=2) :
    Nat.card (ConjClasses (CFSG.Models.A 3 q))≤14 := by
  letI : Fintype q.Field := Fintype.ofFinite q.Field
  have hp := (prime_exponent q hq).1
  letI : CharP q.Field 2 := by rw [←hp]; infer_instance
  have hfield : Fintype.card q.Field=2 := by
    rw [←Nat.card_eq_fintype_card,q.card_field,hq]
  exact BinaryFourProjectivePrimaryClassBound.projective_class_card_le_fourteen hfield

theorem component_class_card_le_twentyEight (q : CFSG.PrimePower) (hq : q.order=2)
    [IsSimpleGroup (CFSG.Models.A 3 q)] :
    Nat.card (ConjClasses (CFSG.Models.A 3 q))*
      Nat.card (Outer (CFSG.Models.A 3 q))≤28 := by
  have hf := (prime_exponent q hq).2
  have ho : Nat.card (Outer (CFSG.Models.A 3 q))≤2 := by
    simpa only [hq,hf] using
      CFSGTypeAOuterGcdCardinality.typeA_higher_outer_card_le_gcd 3 (by decide) q
  exact (Nat.mul_le_mul (class_card_le_fourteen q hq) ho).trans_eq (by decide : 14*2=28)

theorem proper_index_ge_eight (q : CFSG.PrimePower) (hq : q.order=2)
    [IsSimpleGroup (CFSG.Models.A 3 q)]
    (H : Subgroup (CFSG.Models.A 3 q)) (hH : H≠⊤) : 8≤H.index := by
  simpa only [hq] using
    CFSGTypeAProperIndexOrderBudget.typeA_higher_field_power_le_proper_index 3 (by decide) q H hH

theorem proper_index_dvd_20160 (q : CFSG.PrimePower) (hq : q.order=2)
    (H : Subgroup (CFSG.Models.A 3 q)) : H.index ∣ 20160 := by
  simpa only [CFSGTypeARankThreeCardTwo.order_eq_20160 q hq] using H.index_dvd_card

theorem scaled_class_cube_le_proper_index_of_twelve_le (q : CFSG.PrimePower) (hq : q.order=2)
    [IsSimpleGroup (CFSG.Models.A 3 q)]
    (H : Subgroup (CFSG.Models.A 3 q)) (hindex : 12≤H.index) :
    24*(Nat.card (ConjClasses (CFSG.Models.A 3 q))*
      Nat.card (Outer (CFSG.Models.A 3 q)))^3≤3^H.index := by
  exact ((Nat.mul_le_mul_left 24 (Nat.pow_le_pow_left
      (component_class_card_le_twentyEight q hq) 3)).trans
    (by decide +kernel : 24*28^3≤3^12)).trans
      (Nat.pow_le_pow_right (by decide) hindex)

end SymmetricSubgroupAsymptotics.CFSGTypeARankThreeBinaryClassPacket
