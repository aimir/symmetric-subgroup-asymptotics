import SymmetricSubgroupAsymptotics.PrimitiveSocleClassCubeSquareProperGap
import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeARankOneThreeFieldFrontier

/-! Existing trace/torus CLASS-product packets pay the proper-subnormal
extra exponent uniformly in the original PSL2 field family. All factors,
the same subgroup and both degree forms are retained. The literal field
orders four, five and nine remain explicit rather than assumed closed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_pslTwo_even
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hp : q.prime=2) (hq : 8 ≤ q.order)
    (e : D.Simple ≃* CFSG.Models.A 1 q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.A 1 q) := e.symm.isSimpleGroup
  refine D.proper_subnormal_class_cube_le_of_model_square_capacity
    (CFSG.Models.A 1 q) e q.order (by omega) ?_
    (CFSGTypeARankOneEvenClassCube.component_class_cube q hp hq)
    (CFSGTypeARankOneSmallPrimeClassCube.field_square_le_order q (by omega)) H hH hne
  intro K hK
  simpa only [q.card_field] using CFSGPSLTwoEvenPermutationDegree.field_card_le_proper_index
    (F := q.Field) (by simpa only [ringChar.eq q.Field q.prime] using hp) K hK

theorem NonaffineData.proper_subnormal_class_cube_le_of_pslTwo_odd
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : 13 ≤ q.order) (hp : q.prime≠2)
    (e : D.Simple ≃* CFSG.Models.A 1 q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.A 1 q) := e.symm.isSimpleGroup
  refine D.proper_subnormal_class_cube_le_of_model_square_capacity
    (CFSG.Models.A 1 q) e ((q.order+1)/2) (by omega) ?_
    (CFSGTypeARankOneOddClassCube.component_class_cube q hq hp)
    (CFSGTypeARankOneOddClassCube.half_field_square_le_order q (by omega)) H hH hne
  intro K hK
  have hf : q.order ≤ 2*K.index := by
    simpa only [q.card_field] using
      CFSGPSLTwoGeometry.field_card_le_twice_proper_index (F := q.Field) K hK
  omega

theorem NonaffineData.proper_subnormal_class_cube_le_of_pslTwo_small_prime
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hprime : q.order.Prime)
    (hlo : 7 ≤ q.order) (hhi : q.order ≤ 11) (hmod : q.order%4=3)
    (e : D.Simple ≃* CFSG.Models.A 1 q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.A 1 q) := e.symm.isSimpleGroup
  refine D.proper_subnormal_class_cube_le_of_model_square_capacity
    (CFSG.Models.A 1 q) e q.order (by omega) ?_
    (CFSGTypeARankOneSmallPrimeClassCube.component_class_cube q hprime hlo hhi)
    (CFSGTypeARankOneSmallPrimeClassCube.field_square_le_order q (by omega)) H hH hne
  intro K hK
  simpa only [q.card_field] using CFSGPSLTwoThreeModFourPermutationDegree.field_card_le_proper_index
    (F := q.Field) (by simpa only [q.card_field] using hmod) K hK

theorem NonaffineData.proper_subnormal_class_cube_or_pslTwo_three_fields
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : 4 ≤ q.order)
    (e : D.Simple ≃* CFSG.Models.A 1 q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) ∨
      q.order=4 ∨ q.order=5 ∨ q.order=9 := by
  by_cases hlarge : 13 ≤ q.order
  · left
    by_cases heven : q.prime=2
    · exact D.proper_subnormal_class_cube_le_of_pslTwo_even q heven (by omega) e H hH hne
    · exact D.proper_subnormal_class_cube_le_of_pslTwo_odd q hlarge heven e H hH hne
  rcases RankOneRemainingParameterArithmetic.field_parameters q hq (by omega) with
    hexception | heven | hprime | hodd
  · exact Or.inr hexception
  · exact Or.inl (D.proper_subnormal_class_cube_le_of_pslTwo_even
      q heven.1 heven.2 e H hH hne)
  · have hp : q.order.Prime := by rcases hprime with h | h <;> rw [h] <;> decide
    have hlo : 7 ≤ q.order := by rcases hprime with h | h <;> omega
    have hhi : q.order ≤ 11 := by rcases hprime with h | h <;> omega
    have hmod : q.order%4=3 := by rcases hprime with h | h <;> rw [h] <;> decide
    exact Or.inl (D.proper_subnormal_class_cube_le_of_pslTwo_small_prime
      q hp hlo hhi hmod e H hH hne)
  · exact Or.inl (D.proper_subnormal_class_cube_le_of_pslTwo_odd
      q hodd.2 hodd.1 e H hH hne)

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
