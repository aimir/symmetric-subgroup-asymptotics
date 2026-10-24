import SymmetricSubgroupAsymptotics.PrimitiveSocleClassEquationCapacity
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBilinearComponentOrderCube
import SymmetricSubgroupAsymptotics.CFSGUnitaryIsometryComponentOrderCube

/-! One class-equation test refines the original B, D, twisted-D and unitary
component budgets. No new group classification or numerical hypothesis
is hidden: each sufficient arithmetic condition is displayed literally. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ClassicalClassEquationCapacity

def typeB (r : ℕ) (q : CFSG.PrimePower) : Prop :=
  ((q.order^(2*r^2+3*r+1) / q.order^(r-1) + 1) * (3*q.exponent))^3 ≤
    5^(q.order^(r-1)-1)

def typeD (r : ℕ) (q : CFSG.PrimePower) : Prop :=
  ((q.order^(2*r^2+r) / q.order^(r-1) + 1) * (24*q.exponent))^3 ≤
    5^(q.order^(r-1)-1)

def twistedD (r : ℕ) (q : CFSG.PrimePower) : Prop :=
  ((q.order^(2*r^2+r) / q.order^(r-2) + 1) * (8*q.exponent))^3 ≤
    5^(q.order^(r-2)-1)

def unitary (r : ℕ) (q : CFSG.PrimePower) : Prop :=
  ((q.order^((r+1)*(r+2)) / q.order^r + 1) * (2*(r+1)*q.exponent))^3 ≤
    5^(q.order^r-1)

end SymmetricSubgroupAsymptotics.ClassicalClassEquationCapacity

namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction ClassicalClassEquationCapacity
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

private theorem field_two_le (q : CFSG.PrimePower) : 2 ≤ q.order :=
  q.prime_isPrime.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' q.prime)

theorem NonaffineData.subnormal_class_cube_le_of_typeB_class_equation
    (D : NonaffineData G X) (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.B r q) (hbudget : typeB r q)
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.B r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.B r q) := Finite.of_equiv D.Simple e.toEquiv
  refine D.subnormal_class_cube_le_of_model_class_equation_budget
    (CFSG.Models.B r q) e (q.order^(r-1)) (q.order^(2*r^2+3*r+1)) (3*q.exponent) ?_
    (CFSGOrthogonalBOriginalMatrixBounds.typeB_field_power_le_proper_index r hr q)
    (CFSGOrthogonalBBilinearOrderUpper.typeB_order_le_bilinear_power r hr q)
    (CFSGOrthogonalBOriginalMatrixBounds.typeB_outer_card_le_three_exponent r hr q)
    (fun ell hell => (typeB_simpleIndexBounds r hr q ell hell).1) hbudget H hH
  exact (by decide : 3 ≤ 2^2).trans
    ((Nat.pow_le_pow_left (field_two_le q) 2).trans
      (Nat.pow_le_pow_right (by have := field_two_le q; omega) (by omega)))

theorem NonaffineData.subnormal_class_cube_le_of_typeD_class_equation
    (D : NonaffineData G X) (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.D r q) (hbudget : typeD r q)
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.D r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.D r q) := Finite.of_equiv D.Simple e.toEquiv
  refine D.subnormal_class_cube_le_of_model_class_equation_budget
    (CFSG.Models.D r q) e (q.order^(r-1)) (q.order^(2*r^2+r)) (24*q.exponent) ?_
    (CFSGOrthogonalDProperIndexOrderBudget.typeD_field_power_le_proper_index r hr q)
    (CFSGOrthogonalBilinearOrderUpper.typeD_order_le_bilinear_power r hr q)
    (CFSGOrthogonalDProperIndexOrderBudget.typeD_outer_card_le_twentyFour_exponent r hr q)
    (typeD_leastProperIndex_square_lt_card r q hr) hbudget H hH
  exact (by decide : 3 ≤ 2^2).trans
    ((Nat.pow_le_pow_left (field_two_le q) 2).trans
      (Nat.pow_le_pow_right (by have := field_two_le q; omega) (by omega)))

theorem NonaffineData.subnormal_class_cube_le_of_twistedD_class_equation
    (D : NonaffineData G X) (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TwistedD r q) (hbudget : twistedD r q)
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedD r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedD r q) := Finite.of_equiv D.Simple e.toEquiv
  have hnc : ¬IsMulCommutative (CFSG.Models.TwistedD r q) :=
    fun h => D.noncommutative ((isMulCommutative_congr e).mpr h)
  have houter : Nat.card (Outer (CFSG.Models.TwistedD r q)) ≤ 8*q.exponent := by
    obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s+4 := ⟨r-4, by omega⟩
    exact CFSGTwistedDOuterCardinality.original_outer_card_le_eight_exponent s q hnc
  refine D.subnormal_class_cube_le_of_model_class_equation_budget
    (CFSG.Models.TwistedD r q) e (q.order^(r-2)) (q.order^(2*r^2+r))
    (8*q.exponent) ?_
    (CFSGTwistedDProperIndexOrderBudget.typeTwistedD_field_power_le_proper_index r hr q)
    (CFSGOrthogonalBilinearOrderUpper.typeTwistedD_order_le_bilinear_power r hr q)
    houter (typeTwistedD_leastProperIndex_square_lt_card r q hr) hbudget H hH
  exact (by decide : 3 ≤ 2^2).trans
    ((Nat.pow_le_pow_left (field_two_le q) 2).trans
      (Nat.pow_le_pow_right (by have := field_two_le q; omega) (by omega)))

theorem NonaffineData.subnormal_class_cube_le_of_unitary_class_equation
    (D : NonaffineData G X) (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hsmall : r = 2 → q.order ≠ 2) (e : D.Simple ≃* CFSG.Models.TwistedA r q)
    (hbudget : unitary r q) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedA r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedA r q) := Finite.of_equiv D.Simple e.toEquiv
  have hnc : ¬IsMulCommutative (CFSG.Models.TwistedA r q) :=
    fun h => D.noncommutative ((isMulCommutative_congr e).mpr h)
  refine D.subnormal_class_cube_le_of_model_class_equation_budget
    (CFSG.Models.TwistedA r q) e (q.order^r) (q.order^((r+1)*(r+2)))
    (2*(r+1)*q.exponent) ?_
    (CFSGTwistedAUnitaryCoordinates.twistedA_admissible_field_power_le_proper_index r hr q hsmall)
    (CFSGTwistedAUnitaryCoordinates.twistedA_admissible_order_le_isometry_power r hr q hsmall)
    (CFSGTwistedAUnitaryCoordinates.twistedA_admissible_raw_outer_order_le r hr q hsmall hnc)
    (CFSGTwistedAUnitaryCoordinates.twistedA_admissible_leastIndex_square_lt r hr q hsmall)
    hbudget H hH
  exact (by decide : 3 ≤ 2^2).trans
    ((Nat.pow_le_pow_left (field_two_le q) 2).trans
      (Nat.pow_le_pow_right (by have := field_two_le q; omega) hr))

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
