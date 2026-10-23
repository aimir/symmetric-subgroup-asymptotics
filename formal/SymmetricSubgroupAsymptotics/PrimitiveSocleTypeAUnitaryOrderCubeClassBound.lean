import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentOrderCubeClassBound
import SymmetricSubgroupAsymptotics.CFSGTypeAUnitaryComponentOrderCube
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! Concrete original A/unitary parameter tails satisfy the GM cube at
EVERY degree and factor count. All original subgroups are bounded by the
actual ambient order; no subgroup class monotonicity is inferred. The
remaining small field/rank conditions are explicit arithmetic witnesses,
with the rank-one A branch retained separately. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGTypeAUnitaryComponentOrderCube
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

private theorem map_ne_top {S T : Type} [Group S] [Group T]
    (e : S ≃* T) (K : Subgroup S) (hK : K ≠ ⊤) : K.map e.toMonoidHom ≠ ⊤ := by
  intro ht
  apply hK
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm

theorem NonaffineData.subgroup_class_cube_le_of_typeA_capacity
    (D : NonaffineData G X) (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.A r q)
    (hcapacity : 7 ≤ q.order ∨ (4 ≤ q.order ∧ 3 ≤ r) ∨ (3 ≤ q.order ∧ 4 ≤ r) ∨ 7 ≤ r)
    (H : Subgroup G) : Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 1) := by
  letI : IsSimpleGroup (CFSG.Models.A r q) := e.symm.isSimpleGroup
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  refine D.subgroup_class_cube_le_of_component_order_cube (q.order ^ r) ?_ ?_ ?_ ?_ H
  · exact (by decide : 3 ≤ 2 ^ 2).trans
      ((Nat.pow_le_pow_left hq 2).trans (Nat.pow_le_pow_right (by omega) hr))
  · intro K hK
    have hi := CFSGTypeAProperIndexOrderBudget.typeA_higher_field_power_le_proper_index
      r hr q (K.map e.toMonoidHom) (map_ne_top e K hK)
    have he : (K.map e.toMonoidHom).index = K.index := K.index_map_equiv e
    rwa [he] at hi
  · rw [Nat.card_congr e.toEquiv, outer_card_congr e]
    exact typeA_component_order_cube r hr q hcapacity
  · rw [Nat.card_congr e.toEquiv]
    exact typeA_order_ge_1024 r hr q hcapacity

theorem NonaffineData.subgroup_class_cube_le_of_unitary_capacity
    (D : NonaffineData G X) (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hsmall : r = 2 → q.order ≠ 2) (e : D.Simple ≃* CFSG.Models.TwistedA r q)
    (hcapacity : 10 ≤ q.order ∨ (5 ≤ q.order ∧ 3 ≤ r) ∨ (4 ≤ q.order ∧ 4 ≤ r) ∨
      (3 ≤ q.order ∧ 5 ≤ r) ∨ 8 ≤ r)
    (H : Subgroup G) : Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 1) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedA r q) := e.symm.isSimpleGroup
  have hnc : ¬IsMulCommutative (CFSG.Models.TwistedA r q) :=
    fun h => D.noncommutative ((isMulCommutative_congr e).mpr h)
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  refine D.subgroup_class_cube_le_of_component_order_cube (q.order ^ r) ?_ ?_ ?_ ?_ H
  · exact (by decide : 3 ≤ 2 ^ 2).trans
      ((Nat.pow_le_pow_left hq 2).trans (Nat.pow_le_pow_right (by omega) hr))
  · intro K hK
    have hi := CFSGTwistedAUnitaryCoordinates.twistedA_admissible_field_power_le_proper_index
      r hr q hsmall (K.map e.toMonoidHom) (map_ne_top e K hK)
    have he : (K.map e.toMonoidHom).index = K.index := K.index_map_equiv e
    rwa [he] at hi
  · rw [Nat.card_congr e.toEquiv, outer_card_congr e]
    exact unitary_component_order_cube r hr q hsmall hnc hcapacity
  · rw [Nat.card_congr e.toEquiv]
    exact unitary_order_ge_1024 r hr q hsmall hcapacity

theorem NonaffineData.subgroup_class_cube_or_typeA_small_parameters
    (D : NonaffineData G X) (r : ℕ) (hr : 1 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.A r q) (H : Subgroup G) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 1) ∨
      r = 1 ∨ (r = 2 ∧ q.order ≤ 6) ∨ (r = 3 ∧ q.order ≤ 3) ∨
        (4 ≤ r ∧ r ≤ 6 ∧ q.order = 2) := by
  by_cases hone : r = 1
  · exact Or.inr (Or.inl hone)
  have hr2 : 2 ≤ r := by omega
  by_cases hc : 7 ≤ q.order ∨ (4 ≤ q.order ∧ 3 ≤ r) ∨ (3 ≤ q.order ∧ 4 ≤ r) ∨ 7 ≤ r
  · exact Or.inl (D.subgroup_class_cube_le_of_typeA_capacity r hr2 q e hc H)
  · have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
    exact Or.inr (Or.inr (by omega))

theorem NonaffineData.subgroup_class_cube_or_unitary_small_parameters
    (D : NonaffineData G X) (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hsmall : r = 2 → q.order ≠ 2) (e : D.Simple ≃* CFSG.Models.TwistedA r q)
    (H : Subgroup G) : Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 1) ∨
      (r = 2 ∧ q.order ≤ 9) ∨ (r = 3 ∧ q.order ≤ 4) ∨ (r = 4 ∧ q.order ≤ 3) ∨
        (5 ≤ r ∧ r ≤ 7 ∧ q.order = 2) := by
  by_cases hc : 10 ≤ q.order ∨ (5 ≤ q.order ∧ 3 ≤ r) ∨ (4 ≤ q.order ∧ 4 ≤ r) ∨
      (3 ≤ q.order ∧ 5 ≤ r) ∨ 8 ≤ r
  · exact Or.inl (D.subgroup_class_cube_le_of_unitary_capacity r hr q hsmall e hc H)
  · have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
    exact Or.inr (by omega)

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
