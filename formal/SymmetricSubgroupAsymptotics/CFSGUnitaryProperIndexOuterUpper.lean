import SymmetricSubgroupAsymptotics.CFSGUnitaryCompleteOuterBudget
import SymmetricSubgroupAsymptotics.CFSGUnitaryProperIndexOrderUpper

/-! The proved original-model outer reconstruction is bounded by the
square of each actual proper index. Combined with the literal matrix
upper bound, this supplies the socle-plus-outer budget for raw primitive
index forms without a model-specific callback. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open PrimitiveSocleRawStructure

theorem twistedA_admissible_raw_outer_order_le (r : ℕ) (hr : 2 ≤ r)
    (q : CFSG.PrimePower) (hsmall : r=2 → q.order≠2)
    [IsSimpleGroup (CFSG.Models.TwistedA r q)]
    (hn : ¬ IsMulCommutative (CFSG.Models.TwistedA r q)) :
    Nat.card (Outer (CFSG.Models.TwistedA r q)) ≤ 2*(r+1)*q.exponent := by
  by_cases htwo : r=2
  · subst r
    have hq2 : 2 ≤ q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
    have hq : 3 ≤ q.order := by have := hsmall rfl; omega
    simpa only [Nat.reduceAdd,Nat.reduceMul] using
      twistedA_rankTwo_outer_order_le_six_exponent q hq
  · obtain ⟨s,rfl⟩ : ∃ s : ℕ, r=s+3 := ⟨r-3,by omega⟩
    simpa only [Nat.add_assoc,Nat.reduceAdd,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]
      using twistedA_higher_outer_order_le q s hn

theorem twistedA_admissible_outer_order_le_proper_index_square
    (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower) (hsmall : r=2 → q.order≠2)
    [IsSimpleGroup (CFSG.Models.TwistedA r q)]
    (hn : ¬ IsMulCommutative (CFSG.Models.TwistedA r q))
    (H : Subgroup (CFSG.Models.TwistedA r q)) (hH : H≠⊤) :
    Nat.card (Outer (CFSG.Models.TwistedA r q)) ≤ H.index^2 := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hf : q.exponent ≤ q.order :=
    q.exponent.lt_two_pow_self.le.trans
      (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent)
  have hrq : r+1 ≤ q.order^r :=
    (Nat.succ_le_of_lt r.lt_two_pow_self).trans (Nat.pow_le_pow_left hq r)
  have h2q : 2*q.order ≤ q.order^r := by
    calc
      2*q.order ≤ q.order*q.order := Nat.mul_le_mul_right _ hq
      _ = q.order^2 := (pow_two _).symm
      _ ≤ q.order^r := Nat.pow_le_pow_right (by omega) hr
  have hi := twistedA_admissible_field_power_le_proper_index r hr q hsmall H hH
  calc
    Nat.card (Outer (CFSG.Models.TwistedA r q)) ≤ 2*(r+1)*q.exponent :=
      twistedA_admissible_raw_outer_order_le r hr q hsmall hn
    _ ≤ 2*(q.order^r)*q.order := Nat.mul_le_mul
      (Nat.mul_le_mul_left 2 hrq) hf
    _ = q.order^r*(2*q.order) := by ring
    _ ≤ q.order^r*q.order^r := Nat.mul_le_mul_left _ h2q
    _ ≤ H.index*H.index := Nat.mul_le_mul hi hi
    _ = H.index^2 := (pow_two _).symm

theorem twistedA_admissible_order_mul_outer_le_proper_index_log_power
    (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower) (hsmall : r=2 → q.order≠2)
    [IsSimpleGroup (CFSG.Models.TwistedA r q)]
    (hn : ¬ IsMulCommutative (CFSG.Models.TwistedA r q))
    (H : Subgroup (CFSG.Models.TwistedA r q)) (hH : H≠⊤) :
    Nat.card (CFSG.Models.TwistedA r q) *
        Nat.card (Outer (CFSG.Models.TwistedA r q)) ≤ H.index^(4*Nat.log 2 H.index+3) := by
  calc
    Nat.card (CFSG.Models.TwistedA r q) *
        Nat.card (Outer (CFSG.Models.TwistedA r q)) ≤
        H.index^(4*Nat.log 2 H.index+1)*H.index^2 := Nat.mul_le_mul
      (twistedA_admissible_order_le_proper_index_log_power r hr q hsmall H hH)
      (twistedA_admissible_outer_order_le_proper_index_square r hr q hsmall hn H hH)
    _ = H.index^(4*Nat.log 2 H.index+3) := by rw [←pow_add]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
