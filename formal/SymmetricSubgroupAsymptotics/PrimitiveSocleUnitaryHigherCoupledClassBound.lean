import SymmetricSubgroupAsymptotics.CFSGUnitaryHigherCoupledIndex
import SymmetricSubgroupAsymptotics.PrimitiveSocleClassicalClassEquationCapacity
import SymmetricSubgroupAsymptotics.ClassicalClassEquationSmallParameters
import SymmetricSubgroupAsymptotics.UnitaryHigherBinaryClassEquationNumerics

/-! The uniform actual nonabelian point-radical index pays the three
remaining higher binary unitary ranks through the shared class-equation
capacity. The original simple model, factor counts, both degree forms,
and the original subnormal subgroup are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGTwistedAUnitaryCoordinates ClassicalClassEquationCapacity
open UnitaryHigherBinaryClassEquationNumerics
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subnormal_class_cube_le_of_unitary_higher_binary_coupled
    (D : NonaffineData G X) (r : ℕ) (hrange : r=4 ∨ r=5 ∨ r=6)
    (q : CFSG.PrimePower) (hq : q.order=2)
    (e : D.Simple ≃* CFSG.Models.TwistedA r q)
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedA r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedA r q) := Finite.of_equiv D.Simple e.toEquiv
  have hr : 4 ≤ r := by omega
  have hr2 : 2 ≤ r := by omega
  have hsmall : r=2 → q.order≠2 := by omega
  have hnc : ¬IsMulCommutative (CFSG.Models.TwistedA r q) :=
    fun h => D.noncommutative ((isMulCommutative_congr e).mpr h)
  have he : q.exponent=1 := exponent_eq_one_of_prime_order q (by rw [hq]; decide)
  have hp : q.prime=2 := by
    have hpow : q.prime^q.exponent=2 := hq
    rwa [he,pow_one] at hpow
  have hi (K : Subgroup (CFSG.Models.TwistedA r q)) (hK : K≠⊤) :
      coupledBase r ≤ K.index := by
    have hh := twistedA_higher_coupled_proper_index r hr q K hK
    simpa [coupledBase,hq,hp] using hh
  have hc : Nat.card (CFSG.Models.TwistedA r q) ≤ 2^((r+1)*(r+2)) := by
    simpa only [hq] using
      (twistedA_admissible_order_le_isometry_power r hr2 q hsmall)
  have ho : Nat.card (Outer (CFSG.Models.TwistedA r q)) ≤ 2*(r+1) := by
    simpa only [he,Nat.mul_one] using
      (twistedA_admissible_raw_outer_order_le r hr2 q hsmall hnc)
  exact D.subnormal_class_cube_le_of_model_class_equation_budget
    (CFSG.Models.TwistedA r q) e (coupledBase r) (2^((r+1)*(r+2))) (2*(r+1))
    (coupledBase_ge_three r) hi hc ho
    (twistedA_admissible_leastIndex_square_lt r hr2 q hsmall)
    (class_equation_capacity r hrange) H hH

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
