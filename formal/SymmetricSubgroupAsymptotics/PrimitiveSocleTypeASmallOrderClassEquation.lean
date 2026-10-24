import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeAClassEquationCapacity
import SymmetricSubgroupAsymptotics.CFSGProjectiveSpecialLinearOrder
import SymmetricSubgroupAsymptotics.CFSGTypeARankTwoCardTwo

/-! Exact matrix orders and the class-equation template discharge two
further original type-A parameters. No action census, exceptional group
identification, or separate subgroup-class monotonicity is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subnormal_class_cube_le_of_typeA_order_class_budget
    (D : NonaffineData G X) (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.A r q) (b N : ℕ) (hb : 3 ≤ b)
    (hindex : ∀ K : Subgroup (CFSG.Models.A r q), K ≠ ⊤ → b ≤ K.index)
    (hcard : Nat.card (CFSG.Models.A r q) ≤ N)
    (hbudget : ((N / b + 1) * (2 * (q.order-1).gcd (r+1) * q.exponent))^3 ≤ 5^(b-1))
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.A r q) := e.symm.isSimpleGroup
  have hcenterless := (isCenterless_congr e).mp
    (centerless_of_nonabelian_simple D.Simple D.noncommutative)
  have hcenter : Subgroup.center (CFSG.Models.A r q) = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    exact Subgroup.mem_bot.mpr (hcenterless x (fun y => (Subgroup.mem_center_iff.mp hx y).symm))
  have hc := (CFSGConjugacyMinimumIndexBound.class_card_le_div_add_one b (by omega)
    hcenter hindex).trans (Nat.add_le_add_right (Nat.div_le_div_right hcard) 1)
  have ho := CFSGTypeAOuterGcdCardinality.typeA_higher_outer_card_le_gcd r hr q
  refine D.subnormal_class_cube_le_of_model_capacity (CFSG.Models.A r q) e b hb hindex
    ((Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3).trans hbudget) ?_ H hH
  obtain ⟨ell, hell⟩ := exists_leastProperIndex (CFSG.Models.A r q)
  obtain ⟨K, hK, heq⟩ := hell.1
  have hle : b ≤ ell := (hindex K hK).trans_eq heq
  exact (Nat.pow_le_pow_left hle 2).trans
    (CFSGTypeALeastIndexSquare.typeA_leastProperIndex_square_lt_card r hr q ell hell).le

theorem typeA_rank_three_card_three_order (q : CFSG.PrimePower) (hq : q.order = 3) :
    Nat.card (CFSG.Models.A 3 q) = 6065280 := by
  change Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 4) q.Field) = _
  rw [CFSGProjectiveSpecialLinearOrder.projective_card_fin q.Field 4 (by decide),
    q.card_field, hq]
  norm_num [Fin.prod_univ_succ]

theorem typeA_rank_four_card_two_order (q : CFSG.PrimePower) (hq : q.order = 2) :
    Nat.card (CFSG.Models.A 4 q) = 9999360 := by
  change Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 5) q.Field) = _
  rw [CFSGProjectiveSpecialLinearOrder.projective_card_fin q.Field 5 (by decide),
    q.card_field, hq]
  norm_num [Fin.prod_univ_succ]

theorem NonaffineData.subnormal_class_cube_le_of_typeA_rank_three_card_three
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order = 3)
    (e : D.Simple ≃* CFSG.Models.A 3 q) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.A 3 q) := e.symm.isSimpleGroup
  have he : q.exponent = 1 :=
    (Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 3)
      q.exponent_pos.ne' (by decide : (1 : ℕ) ≠ 0)
      (show q.prime^q.exponent = 3^1 from hq)).2
  refine D.subnormal_class_cube_le_of_typeA_order_class_budget 3 (by decide) q e 27 6065280
    (by decide) ?_ (typeA_rank_three_card_three_order q hq).le ?_ H hH
  · intro K hK
    simpa only [hq] using
      CFSGTypeAProperIndexOrderBudget.typeA_higher_field_power_le_proper_index 3 (by decide) q K hK
  · simp only [hq, he]
    decide

theorem NonaffineData.subnormal_class_cube_le_of_typeA_rank_four_card_two
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order = 2)
    (e : D.Simple ≃* CFSG.Models.A 4 q) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.A 4 q) := e.symm.isSimpleGroup
  have he : q.exponent = 1 :=
    (Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 2)
      q.exponent_pos.ne' (by decide : (1 : ℕ) ≠ 0)
      (show q.prime^q.exponent = 2^1 from hq)).2
  refine D.subnormal_class_cube_le_of_typeA_order_class_budget 4 (by decide) q e 31 9999360
    (by decide) ?_ (typeA_rank_four_card_two_order q hq).le ?_ H hH
  · intro K hK
    apply CFSGTypeARankTwoCardTwo.prime_le_proper_index 31 (by decide) _ K hK
    rw [typeA_rank_four_card_two_order q hq]
    decide
  · simp only [hq, he]
    decide

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
