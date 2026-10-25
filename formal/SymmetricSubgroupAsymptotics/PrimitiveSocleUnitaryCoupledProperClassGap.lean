import SymmetricSubgroupAsymptotics.PrimitiveSocleUnitaryProperClassCapacity
import SymmetricSubgroupAsymptotics.PrimitiveSocleUnitaryRankTwoCoupledClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleUnitaryRankThreeCoupledClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleUnitaryHigherCoupledClassBound

/-! The same checked coupled unitary index/order/class-equation packets
pay the proper-subnormal reserve in every remaining small parameter.
All arithmetic capacities below are those of the ordinary packets. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGTwistedAUnitaryCoordinates ClassicalClassEquationCapacity
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

private theorem prime_eq_order_of_exponent_one (q : CFSG.PrimePower)
    (he : q.exponent=1) : q.prime=q.order := by
  change q.prime=q.prime^q.exponent
  rw [he, pow_one]

private theorem prime_eq_two_of_order_four (q : CFSG.PrimePower)
    (hq : q.order=4) : q.prime=2 := by
  have hdiv : q.prime ∣ 2^2 := by
    change q.prime ∣ 4
    rw [← hq]
    exact dvd_pow_self _ q.exponent_pos.ne'
  have htwo : q.prime ∣ 2 := q.prime_isPrime.dvd_of_dvd_pow hdiv
  exact Nat.le_antisymm (Nat.le_of_dvd (by decide) htwo) q.prime_isPrime.two_le

private theorem exponent_le_two_of_order_four (q : CFSG.PrimePower)
    (hq : q.order=4) : q.exponent ≤ 2 := by
  by_contra! he
  have hbig : 8 ≤ q.order := (Nat.pow_le_pow_left q.prime_isPrime.two_le 3).trans
    (Nat.pow_le_pow_right q.prime_isPrime.pos he)
  omega

theorem NonaffineData.proper_subnormal_class_cube_le_of_unitary_rank_two_coupled
    (D : NonaffineData G X) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TwistedA 2 q)
    (hq : q.order=3 ∨ q.order=4 ∨ q.order=5)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedA 2 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedA 2 q) := Finite.of_equiv D.Simple e.toEquiv
  have hlo : 3 ≤ q.order := by omega
  have houter := twistedA_rankTwo_outer_order_le_six_exponent q hlo
  have hdata : ∃ b O : ℕ, 3 ≤ b ∧
      (∀ K : Subgroup (CFSG.Models.TwistedA 2 q), K ≠ ⊤ → b ≤ K.index) ∧
      Nat.card (Outer (CFSG.Models.TwistedA 2 q)) ≤ O ∧
      ((q.order^12/b+1)*O)^3 ≤ 5^(b-1) := by
    rcases hq with hq | hq | hq
    · have he : q.exponent=1 := exponent_eq_one_of_prime_order q (by rw [hq]; decide)
      have hp : q.prime=3 := (prime_eq_order_of_exponent_one q he).trans hq
      refine ⟨27,6,by decide,?_,by simpa only [he] using houter,?_⟩
      · intro K hK
        have hh := twistedA_rankTwo_coupled_proper_index q hlo K hK
        norm_num [hq,hp] at hh
        omega
      · rw [hq]
        decide +kernel
    · have hp := prime_eq_two_of_order_four q hq
      have he := exponent_le_two_of_order_four q hq
      refine ⟨40,12,by decide,?_,houter.trans (Nat.mul_le_mul_left 6 he),?_⟩
      · intro K hK
        have hh := twistedA_rankTwo_coupled_proper_index q hlo K hK
        norm_num [hq,hp] at hh
        omega
      · rw [hq]
        decide +kernel
    · have he : q.exponent=1 := exponent_eq_one_of_prime_order q (by rw [hq]; decide)
      have hp : q.prime=5 := (prime_eq_order_of_exponent_one q he).trans hq
      refine ⟨50,6,by decide,?_,by simpa only [he] using houter,?_⟩
      · intro K hK
        have hh := twistedA_rankTwo_coupled_proper_index q hlo K hK
        norm_num [hq,hp] at hh
        omega
      · rw [hq]
        decide +kernel
  obtain ⟨b,O,hb,hi,ho,hbudget⟩ := hdata
  refine D.proper_subnormal_class_cube_le_of_model_class_equation_capacity
    (CFSG.Models.TwistedA 2 q) e b (q.order^12) O hb hi ?_ ho ?_ hbudget H hH hne
  · exact twistedA_admissible_order_le_isometry_power 2 (by decide) q (by omega)
  · exact twistedA_admissible_leastIndex_square_lt 2 (by decide) q (by omega)

theorem NonaffineData.proper_subnormal_class_cube_le_of_unitary_rank_three_coupled
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=2 ∨ q.order=3)
    (e : D.Simple ≃* CFSG.Models.TwistedA 3 q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedA 3 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedA 3 q) := Finite.of_equiv D.Simple e.toEquiv
  have hr : 2 ≤ (3 : ℕ) := by decide
  have hsmall : (3 : ℕ)=2 → q.order≠2 := by omega
  have hnc : ¬IsMulCommutative (CFSG.Models.TwistedA 3 q) :=
    fun h => D.noncommutative ((isMulCommutative_congr e).mpr h)
  have he : q.exponent=1 := by
    apply exponent_eq_one_of_prime_order q
    rcases hq with hq | hq <;> rw [hq] <;> decide
  have ho : Nat.card (Outer (CFSG.Models.TwistedA 3 q)) ≤ 8 := by
    simpa only [he, Nat.mul_one] using
      (twistedA_admissible_raw_outer_order_le 3 hr q hsmall hnc)
  have hd : ∃ b N : ℕ, 3 ≤ b ∧
      (∀ K : Subgroup (CFSG.Models.TwistedA 3 q), K ≠ ⊤ → b ≤ K.index) ∧
      Nat.card (CFSG.Models.TwistedA 3 q) ≤ N ∧
      ((N/b+1)*8)^3 ≤ 5^(b-1) := by
    rcases hq with hq | hq
    · exact ⟨24,655360,by decide,
        fun K hK => twistedA_rankThree_binary_coupled_proper_index q hq K hK,
        twistedA_rankThree_binary_order_le q hq,UnitaryRankThreeClassEquationNumerics.binary_capacity⟩
    · refine ⟨48,3^20,by decide,
        fun K hK => twistedA_rankThree_ternary_coupled_proper_index q hq K hK,?_,
        UnitaryRankThreeClassEquationNumerics.ternary_capacity⟩
      simpa only [hq] using
        (twistedA_admissible_order_le_isometry_power 3 hr q hsmall)
  obtain ⟨b,N,hb,hi,hN,hbudget⟩ := hd
  exact D.proper_subnormal_class_cube_le_of_model_class_equation_capacity
    (CFSG.Models.TwistedA 3 q) e b N 8 hb hi hN ho
    (twistedA_admissible_leastIndex_square_lt 3 hr q hsmall) hbudget H hH hne

theorem NonaffineData.proper_subnormal_class_cube_le_of_unitary_higher_binary_coupled
    (D : NonaffineData G X) (r : ℕ) (hrange : r=4 ∨ r=5 ∨ r=6)
    (q : CFSG.PrimePower) (hq : q.order=2) (e : D.Simple ≃* CFSG.Models.TwistedA r q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
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
    rwa [he, pow_one] at hpow
  have hi (K : Subgroup (CFSG.Models.TwistedA r q)) (hK : K ≠ ⊤) :
      UnitaryHigherBinaryClassEquationNumerics.coupledBase r ≤ K.index := by
    have hh := twistedA_higher_coupled_proper_index r hr q K hK
    simpa [UnitaryHigherBinaryClassEquationNumerics.coupledBase, hq, hp] using hh
  have hc : Nat.card (CFSG.Models.TwistedA r q) ≤ 2^((r+1)*(r+2)) := by
    simpa only [hq] using
      (twistedA_admissible_order_le_isometry_power r hr2 q hsmall)
  have ho : Nat.card (Outer (CFSG.Models.TwistedA r q)) ≤ 2*(r+1) := by
    simpa only [he, Nat.mul_one] using
      (twistedA_admissible_raw_outer_order_le r hr2 q hsmall hnc)
  exact D.proper_subnormal_class_cube_le_of_model_class_equation_capacity
    (CFSG.Models.TwistedA r q) e (UnitaryHigherBinaryClassEquationNumerics.coupledBase r)
    (2^((r+1)*(r+2))) (2*(r+1))
    (UnitaryHigherBinaryClassEquationNumerics.coupledBase_ge_three r) hi hc ho
    (twistedA_admissible_leastIndex_square_lt r hr2 q hsmall)
    (UnitaryHigherBinaryClassEquationNumerics.class_equation_capacity r hrange) H hH hne

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
