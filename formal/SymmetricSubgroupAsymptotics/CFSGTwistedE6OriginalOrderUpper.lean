import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalFiniteBruhatCover
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPairNormalizerCardinality
import SymmetricSubgroupAsymptotics.CFSGTwistedE6CompleteOuterBudget
import SymmetricSubgroupAsymptotics.CFSGExceptionalOriginalComponentUpper
import SymmetricSubgroupAsymptotics.FiniteFourFactorCoverCardinality

/-! Coarse original twisted-E6 order and outer-order budgets from the
actual fixed Bruhat cover over the quadratic extension. Six ambient scalar
coordinates suffice; their additional fixed-field relations are unnecessary. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6OriginalOrderUpper
open CFSGTwistedE6GeckOriginalFiniteBruhatCover CFSGTwistedE6GeckOriginalPairNormalizer
open CFSGTwistedE6GeckPairNormalizerCardinality CFSGTwistedE6GeckOriginalProjection
open CFSGFFourE6FiniteWeylMenu CFSGTwistedE6GeckOriginalOppositeAlignment
open PrimitiveSocleRawStructure

theorem original_order_le (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (hn : ¬IsMulCommutative (CFSG.Models.TwistedE6 q)) :
    Nat.card (CFSG.Models.TwistedE6 q) ≤ q.order ^ 119 := by
  letI := original_finite q
  let U : Subgroup (CFSG.Models.TwistedE6 q) := originalPositiveSylow q
  let N := originalPairNormalizer q
  have hU : Nat.card U ≤ q.order ^ 48 := originalPositiveSylow_card_le q
  have hN : Nat.card N ≤ q.order ^ 12 := originalPairNormalizer_card_le q hn
  have hcover := FiniteFourFactorCoverCardinality.card_le_of_cover U N U
    (originalMenuWord q) (exists_original_finite_cell q)
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hsmall : 1152 ≤ q.order ^ 11 :=
    (by decide : 1152 ≤ 2 ^ 11).trans (Nat.pow_le_pow_left hq 11)
  calc
    Nat.card (CFSG.Models.TwistedE6 q) ≤
        q.order ^ 48 * q.order ^ 12 * 1152 * q.order ^ 48 :=
      hcover.trans (Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul hU hN) relativeWeylRange_card_le) hU)
    _ = 1152 * q.order ^ 108 := by ring
    _ ≤ q.order ^ 11 * q.order ^ 108 := Nat.mul_le_mul_right _ hsmall
    _ = q.order ^ 119 := by rw [← pow_add]

theorem original_outer_le_cube (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    Nat.card (Outer (CFSG.Models.TwistedE6 q)) ≤ q.order ^ 3 :=
  (CFSGTwistedE6CompleteOuterBudget.typeTwistedE6_outer_card_le_six_exponent q).trans
    (CFSGExceptionalOriginalComponentUpper.six_exponent_le_order_cube q)

theorem original_order_mul_outer_le (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (hn : ¬IsMulCommutative (CFSG.Models.TwistedE6 q)) :
    Nat.card (CFSG.Models.TwistedE6 q) * Nat.card (Outer (CFSG.Models.TwistedE6 q)) ≤
      q.order ^ 122 :=
  (Nat.mul_le_mul (original_order_le q hn) (original_outer_le_cube q)).trans_eq (by ring)

end SymmetricSubgroupAsymptotics.CFSGTwistedE6OriginalOrderUpper
