import SymmetricSubgroupAsymptotics.CFSGTwistedA2InnerTorus
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoTorusKernel
import SymmetricSubgroupAsymptotics.CFSGOuterCardinalityAlignment

/-! Outer cardinality for the literal admissible rank-two twisted-A
model. The faithful pair restriction retains the actual inner torus;
only its proved cube-root projective kernel contributes a factor three.
The original group's simplicity is the sole simplicity assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open PrimitiveSocleRawStructure CFSGOuterCardinalityAlignment

theorem twistedA_rankTwo_outer_order_le_six_exponent (q : CFSG.PrimePower)
    (hq : 3 ≤ q.order) [IsSimpleGroup (CFSG.Models.TwistedA 2 q)] :
    Nat.card (Outer (CFSG.Models.TwistedA 2 q)) ≤ 6 * q.exponent := by
  letI : Finite (CFSG.Models.TwistedA 2 q) :=
    Finite.of_surjective (rankTwoProjectiveCover q hq) (rankTwoProjectiveCover_surjective q hq)
  apply outer_card_le_of_aligned_bound (rankTwoPairStabilizer q hq)
    (rankTwoProjectiveTorus q hq).range
    (rankTwo_inner_align_pair q hq) (rankTwo_inner_torus_mem_pair q hq)
    (rankTwo_inner_torus_injective q hq) (d := 6 * q.exponent)
  calc
    Nat.card (rankTwoPairStabilizer q hq) ≤ (q.order ^ 2 - 1) * (2 * q.exponent) :=
      rankTwo_pairStabilizer_card_le q hq
    _ ≤ (3 * Nat.card (rankTwoProjectiveTorus q hq).range) * (2 * q.exponent) :=
      Nat.mul_le_mul_right _ (rankTwoProjectiveTorus_card_lower q hq)
    _ = Nat.card (rankTwoProjectiveTorus q hq).range * (6 * q.exponent) := by ring

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
