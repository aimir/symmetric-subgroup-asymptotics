import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoCoupledIndex
import SymmetricSubgroupAsymptotics.PrimitiveSocleClassicalClassEquationCapacity
import SymmetricSubgroupAsymptotics.ClassicalClassEquationSmallParameters

/-! The actual coupled rank-two unitary index closes field orders 3,4,5
through the shared class-equation capacity. The original coarse outer
bound 6f already suffices after class-equation division; no sharper
automorphism theorem is an assumption of this consumer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGTwistedAUnitaryCoordinates ClassicalClassEquationCapacity
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

private theorem prime_eq_order_of_exponent_one (q : CFSG.PrimePower)
    (he : q.exponent = 1) : q.prime = q.order := by
  change q.prime = q.prime^q.exponent
  rw [he,pow_one]

private theorem prime_eq_two_of_order_four (q : CFSG.PrimePower)
    (hq : q.order = 4) : q.prime = 2 := by
  have hdiv : q.prime ∣ 2^2 := by
    change q.prime ∣ 4
    rw [← hq]
    exact dvd_pow_self _ q.exponent_pos.ne'
  have htwo : q.prime ∣ 2 := q.prime_isPrime.dvd_of_dvd_pow hdiv
  exact Nat.le_antisymm (Nat.le_of_dvd (by decide) htwo) q.prime_isPrime.two_le

private theorem exponent_le_two_of_order_four (q : CFSG.PrimePower)
    (hq : q.order = 4) : q.exponent ≤ 2 := by
  by_contra! he
  have hbig : 8 ≤ q.order := (Nat.pow_le_pow_left q.prime_isPrime.two_le 3).trans
    (Nat.pow_le_pow_right q.prime_isPrime.pos he)
  omega

theorem NonaffineData.subnormal_class_cube_le_of_unitary_rank_two_coupled
    (D : NonaffineData G X) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TwistedA 2 q)
    (hq : q.order = 3 ∨ q.order = 4 ∨ q.order = 5)
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedA 2 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedA 2 q) := Finite.of_equiv D.Simple e.toEquiv
  have hlo : 3 ≤ q.order := by omega
  have houter := twistedA_rankTwo_outer_order_le_six_exponent q hlo
  have hdata : ∃ b O : ℕ, 3 ≤ b ∧
      (∀ K : Subgroup (CFSG.Models.TwistedA 2 q), K ≠ ⊤ → b ≤ K.index) ∧
      Nat.card (Outer (CFSG.Models.TwistedA 2 q)) ≤ O ∧
      ((q.order^12/b+1)*O)^3 ≤ 5^(b-1) := by
    rcases hq with hq | hq | hq
    · have he : q.exponent = 1 := exponent_eq_one_of_prime_order q (by rw [hq]; decide)
      have hp : q.prime = 3 := (prime_eq_order_of_exponent_one q he).trans hq
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
    · have he : q.exponent = 1 := exponent_eq_one_of_prime_order q (by rw [hq]; decide)
      have hp : q.prime = 5 := (prime_eq_order_of_exponent_one q he).trans hq
      refine ⟨50,6,by decide,?_,by simpa only [he] using houter,?_⟩
      · intro K hK
        have hh := twistedA_rankTwo_coupled_proper_index q hlo K hK
        norm_num [hq,hp] at hh
        omega
      · rw [hq]
        decide +kernel
  obtain ⟨b,O,hb,hi,ho,hbudget⟩ := hdata
  refine D.subnormal_class_cube_le_of_model_class_equation_budget
    (CFSG.Models.TwistedA 2 q) e b (q.order^12) O hb hi ?_ ho ?_ hbudget H hH
  · exact twistedA_admissible_order_le_isometry_power 2 (by decide) q (by omega)
  · exact twistedA_admissible_leastIndex_square_lt 2 (by decide) q (by omega)

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
