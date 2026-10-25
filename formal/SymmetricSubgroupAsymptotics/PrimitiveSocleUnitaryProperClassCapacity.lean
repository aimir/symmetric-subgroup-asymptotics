import SymmetricSubgroupAsymptotics.PrimitiveSocleModelProperClassCapacity
import SymmetricSubgroupAsymptotics.PrimitiveSocleUnitaryIsometryOrderCubeClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleClassicalClassEquationCapacity

/-! The proved actual unitary isometry and class-equation capacities
feed the same proper-subnormal reserves. No new field/rank inequality
or larger comparison group is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGTwistedAUnitaryCoordinates
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_unitary_isometry_capacity
    (D : NonaffineData G X) (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hsmall : r=2 → q.order≠2) (e : D.Simple ≃* CFSG.Models.TwistedA r q)
    (hc : UnitaryIsometryOrderCubeNumerics.Capacity q.order r)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedA r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedA r q) := Finite.of_equiv D.Simple e.toEquiv
  have hnc : ¬IsMulCommutative (CFSG.Models.TwistedA r q) :=
    fun h => D.noncommutative ((isMulCommutative_congr e).mpr h)
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  exact D.proper_subnormal_class_cube_le_of_model_order_capacity
    (CFSG.Models.TwistedA r q) e (q.order^r)
    ((by decide : 3 ≤ 2^2).trans
      ((Nat.pow_le_pow_left hq 2).trans (Nat.pow_le_pow_right (by omega) hr)))
    (twistedA_admissible_field_power_le_proper_index r hr q hsmall)
    (CFSGUnitaryIsometryComponentOrderCube.component_order_cube r hr q hsmall hnc hc)
    (CFSGUnitaryIsometryComponentOrderCube.order_ge_1024 r hr q hsmall hc) H hH hne

theorem NonaffineData.proper_subnormal_class_cube_le_of_unitary_class_equation
    (D : NonaffineData G X) (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hsmall : r=2 → q.order≠2) (e : D.Simple ≃* CFSG.Models.TwistedA r q)
    (hbudget : ClassicalClassEquationCapacity.unitary r q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedA r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedA r q) := Finite.of_equiv D.Simple e.toEquiv
  have hnc : ¬IsMulCommutative (CFSG.Models.TwistedA r q) :=
    fun h => D.noncommutative ((isMulCommutative_congr e).mpr h)
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  exact D.proper_subnormal_class_cube_le_of_model_class_equation_capacity
    (CFSG.Models.TwistedA r q) e (q.order^r) (q.order^((r+1)*(r+2)))
    (2*(r+1)*q.exponent)
    ((by decide : 3 ≤ 2^2).trans
      ((Nat.pow_le_pow_left hq 2).trans (Nat.pow_le_pow_right (by omega) hr)))
    (twistedA_admissible_field_power_le_proper_index r hr q hsmall)
    (twistedA_admissible_order_le_isometry_power r hr q hsmall)
    (twistedA_admissible_raw_outer_order_le r hr q hsmall hnc)
    (twistedA_admissible_leastIndex_square_lt r hr q hsmall) hbudget H hH hne

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
