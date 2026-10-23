import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalOrderUpper
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalOuterBound
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckPermutationDegree

/-! An actual bounded component budget at EVERY original proper index. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckProperIndexOrderBudget
open CFSGTrialityGeckOriginalOrderUpper CFSGTrialityGeckOriginalOuterBound
open CFSGTrialityGeckPermutationDegree PrimitiveSocleRawStructure
open CFSGTrialityGeckGeneratedOriginalProjection

local instance (q:CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    Finite (CFSG.Models.TrialityD4 q) := Finite.of_surjective
  (generatedToOriginal q) (generatedToOriginal_surjective q)

theorem order_le_proper_index (q:CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    (H:Subgroup (CFSG.Models.TrialityD4 q)) (hH:H≠⊤) : q.order≤H.index := by
  have hq : 2≤q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hc := order_cube_le_twice_proper_index q H hH
  have hs : 2≤q.order^2 := (by decide : 2≤2^2).trans (Nat.pow_le_pow_left hq 2)
  have hh : 2*q.order≤q.order^3 :=
    (Nat.mul_le_mul_right q.order hs).trans_eq (pow_succ q.order 2).symm
  omega

theorem original_outer_card_le_power (q:CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    Nat.card (Outer (CFSG.Models.TrialityD4 q))≤q.order^3 := by
  have hq : 2≤q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hf : q.exponent≤q.order := q.exponent.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent)
  have h3 : 3≤q.order^2 := (by decide : 3≤2^2).trans (Nat.pow_le_pow_left hq 2)
  calc
    Nat.card (Outer (CFSG.Models.TrialityD4 q))≤3*q.exponent :=
      original_outer_card_le_three_exponent q
    _≤3*q.order := Nat.mul_le_mul_left _ hf
    _≤q.order^2*q.order := Nat.mul_le_mul_right _ h3
    _=q.order^3 := (pow_succ _ 2).symm

theorem original_order_mul_outer_le_proper_index_power (q:CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    (hn:¬IsMulCommutative (CFSG.Models.TrialityD4 q))
    (H:Subgroup (CFSG.Models.TrialityD4 q)) (hH:H≠⊤) :
    Nat.card (CFSG.Models.TrialityD4 q)*Nat.card (Outer (CFSG.Models.TrialityD4 q))≤H.index^66 := by
  have hi := order_le_proper_index q H hH
  calc
    Nat.card (CFSG.Models.TrialityD4 q)*Nat.card (Outer (CFSG.Models.TrialityD4 q))≤
      q.order^32*q.order^3 := Nat.mul_le_mul
        (original_order_le_power q hn) (original_outer_card_le_power q)
    _=q.order^35 := by ring
    _≤H.index^35 := Nat.pow_le_pow_left hi 35
    _≤H.index^66 := Nat.pow_le_pow_right (by have := H.one_lt_index_of_ne_top hH;omega) (by decide)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckProperIndexOrderBudget
