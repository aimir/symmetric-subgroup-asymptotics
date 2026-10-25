import SymmetricSubgroupAsymptotics.PrimitiveSocleModelProperClassCapacity
import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeAUnitaryOrderCubeClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeABinaryCyclicClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeASmallOrderClassEquation

/-! Higher-A proper-gap packets reuse exactly the checked ordinary
order, cyclic-code and class-equation capacities. No new parameter
range, action census or exceptional model identification is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGTypeAUnitaryComponentOrderCube
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_typeA_capacity
    (D : NonaffineData G X) (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.A r q)
    (hcapacity : 7 ≤ q.order ∨ (4 ≤ q.order ∧ 3 ≤ r) ∨ (3 ≤ q.order ∧ 4 ≤ r) ∨ 7 ≤ r)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.A r q) := e.symm.isSimpleGroup
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  exact D.proper_subnormal_class_cube_le_of_model_order_capacity
    (CFSG.Models.A r q) e (q.order^r)
    ((by decide : 3 ≤ 2^2).trans
      ((Nat.pow_le_pow_left hq 2).trans (Nat.pow_le_pow_right (by omega) hr)))
    (CFSGTypeAProperIndexOrderBudget.typeA_higher_field_power_le_proper_index r hr q)
    (typeA_component_order_cube r hr q hcapacity)
    (typeA_order_ge_1024 r hr q hcapacity) H hH hne

theorem NonaffineData.proper_subnormal_class_cube_le_of_typeA_binary_cyclic
    (D : NonaffineData G X) (r : ℕ) (hr : r=3 ∨ r=5)
    (q : CFSG.PrimePower) (hq : q.order=2) (e : D.Simple ≃* CFSG.Models.A r q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.A r q) := e.symm.isSimpleGroup
  letI : Fintype q.Field := Fintype.ofFinite _
  have hK : Fintype.card q.Field=2 := by
    rw [← Nat.card_eq_fintype_card, q.card_field, hq]
  have he : q.exponent=1 :=
    (Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 2)
      q.exponent_pos.ne' (by decide : (1 : ℕ)≠0)
      (show q.prime^q.exponent=2^1 from hq)).2
  have hrlo : 2 ≤ r := by omega
  have hc : Nat.card (ConjClasses (CFSG.Models.A r q)) ≤
      (BinaryWeightedMultisetCodes.codes (r+1)).card := by
    simpa only [Fintype.card_fin] using
      BinaryProjectiveLinearClassBound.projective_class_card_le_codes (I:=Fin (r+1)) hK
  have ho : Nat.card (Outer (CFSG.Models.A r q)) ≤ 2 := by
    simpa [hq, he] using
      CFSGTypeAOuterGcdCardinality.typeA_higher_outer_card_le_gcd r hrlo q
  have hi : ∀ K : Subgroup (CFSG.Models.A r q), K ≠ ⊤ → 2^r ≤ K.index := by
    intro K hK
    simpa only [hq] using
      CFSGTypeAProperIndexOrderBudget.typeA_higher_field_power_le_proper_index r hrlo q K hK
  have hb : 3 ≤ 2^r := (by decide : 3 ≤ 2^2).trans
    (Nat.pow_le_pow_right (by decide : 0<2) hrlo)
  have hbudget : ((BinaryWeightedMultisetCodes.codes (r+1)).card*2)^3 ≤ 5^(2^r-1) := by
    rcases hr with rfl | rfl
    · rw [show 3+1=4 from rfl, BinaryWeightedMultisetCodes.card_codes_four]
      decide
    · rw [show 5+1=6 from rfl, BinaryWeightedMultisetCodes.card_codes_six]
      decide
  refine D.proper_subnormal_class_cube_le_of_model_square_capacity
    (CFSG.Models.A r q) e (2^r) hb hi
    ((Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3).trans hbudget) ?_ H hH hne
  obtain ⟨ell, hell⟩ := exists_leastProperIndex (CFSG.Models.A r q)
  obtain ⟨K, hK, heq⟩ := hell.1
  exact (Nat.pow_le_pow_left ((hi K hK).trans_eq heq) 2).trans
    (CFSGTypeALeastIndexSquare.typeA_leastProperIndex_square_lt_card r hrlo q ell hell).le

theorem NonaffineData.proper_subnormal_class_cube_le_of_typeA_order_class_budget
    (D : NonaffineData G X) (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.A r q) (b N : ℕ) (hb : 3 ≤ b)
    (hindex : ∀ K : Subgroup (CFSG.Models.A r q), K ≠ ⊤ → b ≤ K.index)
    (hcard : Nat.card (CFSG.Models.A r q) ≤ N)
    (hbudget : ((N/b+1)*(2*(q.order-1).gcd (r+1)*q.exponent))^3 ≤ 5^(b-1))
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.A r q) := e.symm.isSimpleGroup
  exact D.proper_subnormal_class_cube_le_of_model_class_equation_capacity
    (CFSG.Models.A r q) e b N (2*(q.order-1).gcd (r+1)*q.exponent) hb hindex hcard
    (CFSGTypeAOuterGcdCardinality.typeA_higher_outer_card_le_gcd r hr q)
    (CFSGTypeALeastIndexSquare.typeA_leastProperIndex_square_lt_card r hr q)
    hbudget H hH hne

theorem NonaffineData.proper_subnormal_class_cube_le_of_typeA_rank_three_card_three
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=3)
    (e : D.Simple ≃* CFSG.Models.A 3 q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.A 3 q) := e.symm.isSimpleGroup
  have he : q.exponent=1 :=
    (Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 3)
      q.exponent_pos.ne' (by decide : (1 : ℕ)≠0)
      (show q.prime^q.exponent=3^1 from hq)).2
  refine D.proper_subnormal_class_cube_le_of_typeA_order_class_budget
    3 (by decide) q e 27 6065280 (by decide) ?_
    (typeA_rank_three_card_three_order q hq).le ?_ H hH hne
  · intro K hK
    simpa only [hq] using
      CFSGTypeAProperIndexOrderBudget.typeA_higher_field_power_le_proper_index 3 (by decide) q K hK
  · simp only [hq, he]
    decide

theorem NonaffineData.proper_subnormal_class_cube_le_of_typeA_rank_four_card_two
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=2)
    (e : D.Simple ≃* CFSG.Models.A 4 q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.A 4 q) := e.symm.isSimpleGroup
  have he : q.exponent=1 :=
    (Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 2)
      q.exponent_pos.ne' (by decide : (1 : ℕ)≠0)
      (show q.prime^q.exponent=2^1 from hq)).2
  refine D.proper_subnormal_class_cube_le_of_typeA_order_class_budget
    4 (by decide) q e 31 9999360 (by decide) ?_
    (typeA_rank_four_card_two_order q hq).le ?_ H hH hne
  · intro K hK
    apply CFSGTypeARankTwoCardTwo.prime_le_proper_index 31 (by decide) _ K hK
    rw [typeA_rank_four_card_two_order q hq]
    decide
  · simp only [hq, he]
    decide

theorem NonaffineData.proper_subnormal_class_cube_le_of_typeA_rank_six_card_two
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=2)
    (e : D.Simple ≃* CFSG.Models.A 6 q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.A 6 q) := e.symm.isSimpleGroup
  have he : q.exponent=1 :=
    (Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 2)
      q.exponent_pos.ne' (by decide : (1 : ℕ)≠0)
      (show q.prime^q.exponent=2^1 from hq)).2
  refine D.proper_subnormal_class_cube_le_of_typeA_order_class_budget
    6 (by decide) q e (q.order^6) (q.order^((6+1)^2)) ?_
    (CFSGTypeAProperIndexOrderBudget.typeA_higher_field_power_le_proper_index 6 (by decide) q)
    (typeA_order_le_matrix_power 6 q) ?_ H hH hne
  · rw [hq]
    decide
  · simp only [hq, he]
    decide

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
