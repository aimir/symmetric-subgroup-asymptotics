import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentOrderCubeClassBound
import SymmetricSubgroupAsymptotics.CFSGUnitaryIsometryComponentOrderCube
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The actual isometry order cube sharpens the original unitary
primitive consumer for every factor count and every subgroup. Original
socle data, model equivalence and proper-index witnesses are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGUnitaryIsometryComponentOrderCube
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

private theorem map_ne_top {S T : Type} [Group S] [Group T]
    (e : S ≃* T) (K : Subgroup S) (hK : K≠⊤) : K.map e.toMonoidHom≠⊤ := by
  intro ht
  apply hK
  apply Subgroup.map_injective (f:=e.toMonoidHom) e.injective
  exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm

theorem NonaffineData.subgroup_class_cube_le_of_unitary_isometry_capacity
    (D : NonaffineData G X) (r : ℕ) (hr : 2≤r) (q : CFSG.PrimePower)
    (hsmall : r=2 → q.order≠2) (e : D.Simple ≃* CFSG.Models.TwistedA r q)
    (hc : UnitaryIsometryOrderCubeNumerics.Capacity q.order r) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedA r q) := e.symm.isSimpleGroup
  have hnc : ¬IsMulCommutative (CFSG.Models.TwistedA r q) :=
    fun h => D.noncommutative ((isMulCommutative_congr e).mpr h)
  have hq : 2≤q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  refine D.subgroup_class_cube_le_of_component_order_cube (q.order^r) ?_ ?_ ?_ ?_ H
  · exact (by decide : 3≤2^2).trans
      ((Nat.pow_le_pow_left hq 2).trans (Nat.pow_le_pow_right (by omega) hr))
  · intro K hK
    have hi := CFSGTwistedAUnitaryCoordinates.twistedA_admissible_field_power_le_proper_index
      r hr q hsmall (K.map e.toMonoidHom) (map_ne_top e K hK)
    have he : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    rwa [he] at hi
  · rw [Nat.card_congr e.toEquiv,outer_card_congr e]
    exact component_order_cube r hr q hsmall hnc hc
  · rw [Nat.card_congr e.toEquiv]
    exact order_ge_1024 r hr q hsmall hc

theorem NonaffineData.subgroup_class_cube_or_unitary_isometry_small_parameters
    (D : NonaffineData G X) (r : ℕ) (hr : 2≤r) (q : CFSG.PrimePower)
    (hsmall : r=2 → q.order≠2) (e : D.Simple ≃* CFSG.Models.TwistedA r q)
    (H : Subgroup G) : Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) ∨
      (r=2 ∧ q.order≤7) ∨ (r=3 ∧ q.order≤3) ∨ (4≤r ∧ r≤6 ∧ q.order=2) := by
  by_cases hc : UnitaryIsometryOrderCubeNumerics.Capacity q.order r
  · exact Or.inl (D.subgroup_class_cube_le_of_unitary_isometry_capacity r hr q hsmall e hc H)
  · have hq : 2≤q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
    exact Or.inr (UnitaryIsometryOrderCubeNumerics.small_parameters_of_not_capacity
      q.order r hq hr hc)

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
