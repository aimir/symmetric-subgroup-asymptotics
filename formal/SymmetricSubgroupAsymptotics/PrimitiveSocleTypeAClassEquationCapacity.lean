import SymmetricSubgroupAsymptotics.CFSGConjugacyMinimumIndexBound
import SymmetricSubgroupAsymptotics.CFSGTypeAOuterGcdCardinality
import SymmetricSubgroupAsymptotics.CFSGTypeAProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGTypeALeastIndexSquare
import SymmetricSubgroupAsymptotics.CFSGTypeAMinimumIndexLower
import SymmetricSubgroupAsymptotics.PrimitiveSocleModelClassCubeSquareClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart

/-! A uniform class-equation capacity test on the original type-A model.
It combines the actual matrix order bound with the actual proper-index
bound, instead of charging every group element as a conjugacy class.
Both original primitive degree forms and the actual subnormal subgroup
are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subnormal_class_cube_le_of_typeA_class_equation_budget
    (D : NonaffineData G X) (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.A r q)
    (hbudget : ((q.order ^ ((r+1)^2) / q.order^r + 1) *
      (2 * (q.order-1).gcd (r+1) * q.exponent))^3 ≤ 5^(q.order^r-1))
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.A r q) := e.symm.isSimpleGroup
  have hcenterless := (isCenterless_congr e).mp
    (centerless_of_nonabelian_simple D.Simple D.noncommutative)
  have hcenter : Subgroup.center (CFSG.Models.A r q) = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    exact Subgroup.mem_bot.mpr (hcenterless x (fun y => (Subgroup.mem_center_iff.mp hx y).symm))
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  have hindex := CFSGTypeAProperIndexOrderBudget.typeA_higher_field_power_le_proper_index r hr q
  have hclass := CFSGConjugacyMinimumIndexBound.class_card_le_div_add_one
    (q.order^r) (pow_pos (by omega) _) hcenter hindex
  have hc : Nat.card (ConjClasses (CFSG.Models.A r q)) ≤
      q.order^((r+1)^2) / q.order^r + 1 := hclass.trans
    (Nat.add_le_add_right (Nat.div_le_div_right (typeA_order_le_matrix_power r q)) 1)
  have ho := CFSGTypeAOuterGcdCardinality.typeA_higher_outer_card_le_gcd r hr q
  have hb : 3 ≤ q.order^r := (by decide : 3 ≤ 2^2).trans
    ((Nat.pow_le_pow_left hq 2).trans (Nat.pow_le_pow_right (by omega) hr))
  refine D.subnormal_class_cube_le_of_model_capacity (CFSG.Models.A r q) e
    (q.order^r) hb hindex
    ((Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3).trans hbudget) ?_ H hH
  obtain ⟨ell, hell⟩ := exists_leastProperIndex (CFSG.Models.A r q)
  exact (Nat.pow_le_pow_left
    (CFSGTypeAMinimumIndexLower.order_power_le_leastProperIndex r hr q ell hell) 2).trans
    (CFSGTypeALeastIndexSquare.typeA_leastProperIndex_square_lt_card r hr q ell hell).le

theorem NonaffineData.subnormal_class_cube_le_of_typeA_rank_six_card_two
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order = 2)
    (e : D.Simple ≃* CFSG.Models.A 6 q) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  have he : q.exponent = 1 :=
    (Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 2)
      q.exponent_pos.ne' (by decide : (1 : ℕ) ≠ 0)
      (show q.prime^q.exponent = 2^1 from hq)).2
  refine D.subnormal_class_cube_le_of_typeA_class_equation_budget 6 (by decide) q e ?_ H hH
  simp only [hq, he]
  decide

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
