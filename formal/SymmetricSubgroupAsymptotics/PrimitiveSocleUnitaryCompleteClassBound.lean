import SymmetricSubgroupAsymptotics.PrimitiveSocleUnitaryRankThreeCoupledClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleUnitaryRankTwoCoupledClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleUnitaryHigherCoupledClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleUnitaryIsometryOrderCubeClassBound
import SymmetricSubgroupAsymptotics.CFSGPrimePowerSmallOrders

/-! Every admissible unitary rank and field is paid on the same original
simple model, preserving both raw degree forms and the subnormal group.
The residual small fields are exhausted arithmetically, without any
permutation-action or subgroup catalogue. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGTwistedAUnitaryCoordinates ClassicalClassEquationCapacity
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subnormal_class_cube_le_of_unitary_all_fields
    (D : NonaffineData G X) (r : ℕ) (hr : 2≤r) (q : CFSG.PrimePower)
    (hsmall : r=2 → q.order≠2) (e : D.Simple ≃* CFSG.Models.TwistedA r q)
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  rcases D.subgroup_class_cube_or_unitary_isometry_small_parameters
      r hr q hsmall e H with hc | hp
  · exact hc
  · rcases hp with ⟨rfl,hq⟩ | ⟨rfl,hq⟩ | ⟨hrlo,hrhi,hq⟩
    · rcases CFSGPrimePowerSmallOrders.order_le_seven_cases q hq with
        htwo | hthree | hfour | hfive | hseven
      · exact (hsmall rfl htwo).elim
      · exact D.subnormal_class_cube_le_of_unitary_rank_two_coupled q e
          (Or.inl hthree) H hH
      · exact D.subnormal_class_cube_le_of_unitary_rank_two_coupled q e
          (Or.inr (Or.inl hfour)) H hH
      · exact D.subnormal_class_cube_le_of_unitary_rank_two_coupled q e
          (Or.inr (Or.inr hfive)) H hH
      · exact D.subnormal_class_cube_le_of_unitary_class_equation 2 hr q hsmall e
          (unitary_rank_two_seven q hseven) H hH
    · have hlo : 2≤q.order := q.prime_isPrime.two_le.trans
        (Nat.le_self_pow q.exponent_pos.ne' q.prime)
      exact D.subnormal_class_cube_le_of_unitary_rank_three_coupled q (by omega) e H hH
    · exact D.subnormal_class_cube_le_of_unitary_higher_binary_coupled
        r (by omega) q hq e H hH

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
