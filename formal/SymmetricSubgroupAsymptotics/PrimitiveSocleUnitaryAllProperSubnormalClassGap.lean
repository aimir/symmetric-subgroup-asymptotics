import SymmetricSubgroupAsymptotics.PrimitiveSocleUnitaryCoupledProperClassGap
import SymmetricSubgroupAsymptotics.CFSGPrimePowerSmallOrders

/-! All admissible original unitary models pay the proper-subnormal
extra gap. The existing isometry-capacity arithmetic leaves exactly
the checked coupled small fields; both degree forms remain literal. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_unitary_all_fields
    (D : NonaffineData G X) (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hsmall : r=2 → q.order≠2) (e : D.Simple ≃* CFSG.Models.TwistedA r q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  by_cases hc : UnitaryIsometryOrderCubeNumerics.Capacity q.order r
  · exact D.proper_subnormal_class_cube_le_of_unitary_isometry_capacity
      r hr q hsmall e hc H hH hne
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  have hp := UnitaryIsometryOrderCubeNumerics.small_parameters_of_not_capacity
    q.order r hq hr hc
  rcases hp with ⟨rfl,hfield⟩ | ⟨rfl,hfield⟩ | ⟨hrlo,hrhi,hfield⟩
  · rcases CFSGPrimePowerSmallOrders.order_le_seven_cases q hfield with
      htwo | hthree | hfour | hfive | hseven
    · exact (hsmall rfl htwo).elim
    · exact D.proper_subnormal_class_cube_le_of_unitary_rank_two_coupled
        q e (Or.inl hthree) H hH hne
    · exact D.proper_subnormal_class_cube_le_of_unitary_rank_two_coupled
        q e (Or.inr (Or.inl hfour)) H hH hne
    · exact D.proper_subnormal_class_cube_le_of_unitary_rank_two_coupled
        q e (Or.inr (Or.inr hfive)) H hH hne
    · exact D.proper_subnormal_class_cube_le_of_unitary_class_equation
        2 (by decide) q hsmall e
        (ClassicalClassEquationCapacity.unitary_rank_two_seven q hseven) H hH hne
  · exact D.proper_subnormal_class_cube_le_of_unitary_rank_three_coupled
      q (by omega) e H hH hne
  · exact D.proper_subnormal_class_cube_le_of_unitary_higher_binary_coupled
      r (by omega) q hfield e H hH hne

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
