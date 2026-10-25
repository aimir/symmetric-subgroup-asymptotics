import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorTwiceQuadraticSylowTail
import SymmetricSubgroupAsymptotics.PGroupCardPowerDivisibility
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckFixedBruhatOrderUpper
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointIndex
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalGoodSylow
import SymmetricSubgroupAsymptotics.CFSGGTwoCompleteOuterBudget
import SymmetricSubgroupAsymptotics.SimpleLeastIndexStrictOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! Actual original G2 positive-Sylow and index bounds pay the
one-factor ordinary tail. The q=3 endpoint is obtained from the same
model's order lower bound and faithful least-index coset action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleGTwoOneFactorOrdinaryTail
open PrimitiveSocleRawStructure CFSGGTwoD4GeckOriginalProjection

private theorem field_square_le_index (q : CFSG.PrimePower) (hsmall : q.order ≠ 2)
    [IsSimpleGroup (CFSG.Models.G2 q)] [Finite (CFSG.Models.G2 q)]
    (ell : ℕ) (hell : LeastProperIndex (CFSG.Models.G2 q) ell) : q.order ^ 2 ≤ ell := by
  have hq2 : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  by_cases hthree : q.order = 3
  · have hcard : 3 ^ 12 ≤ Nat.card (CFSG.Models.G2 q) := by
      have hh := original_order_lower q.Field
      simpa only [q.card_field, hthree] using hh
    have hdvd := SimpleLeastIndexStrictOrdinaryGenerators.card_dvd_factorial
      (CFSG.Models.G2 q) ell hell
    have hle := Nat.le_of_dvd (Nat.factorial_pos ell) hdvd
    have hnine : 9 ≤ ell := by
      by_contra hn
      have hf : ell.factorial ≤ (8 : ℕ).factorial := Nat.factorial_le (by omega)
      norm_num only [show (8 : ℕ).factorial = 40320 by decide] at hf
      norm_num only [show (3 : ℕ)^12 = 531441 by decide] at hcard
      omega
    simpa only [hthree, show (3 : ℕ)^2 = 9 by decide] using hnine
  · obtain ⟨H, hH, he⟩ := hell.1
    by_cases hchar : q.prime = 3
    · have hq4 : 4 ≤ q.order := by omega
      have hi := CFSGGTwoD4GeckMiddleEndpointIndex.typeGTwo_char_three_le_proper_index
        q hchar hq4 H hH
      have hsquare : 2 ≤ q.order ^ 2 :=
        (by decide : 2 ≤ (4 : ℕ)^2).trans (Nat.pow_le_pow_left hq4 2)
      have hbound : q.order ^ 2 ≤ 3 * (q.order ^ 2 - 1) := by omega
      exact hbound.trans (hi.trans_eq he)
    · have hi := CFSGGTwoD4GeckMiddlePairingIndex.typeGTwo_middle_le_proper_index q hchar H hH
      exact (Nat.le_mul_of_pos_left _ q.prime_isPrime.pos).trans (hi.trans_eq he)

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling (hk : D.factorCount = 1) (q : CFSG.PrimePower)
    (hsmall : q.order ≠ 2) (e : D.Simple ≃* CFSG.Models.G2 q)
    (hn : 1024 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : IsSimpleGroup (CFSG.Models.G2 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.G2 q) := Finite.of_equiv D.Simple e.toEquiv
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  obtain ⟨ell, hell⟩ := exists_leastProperIndex D.Simple
  have hellM := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
  have hfield : q.order ^ 2 ≤ ell := field_square_le_index q hsmall ell hellM
  let P := originalPositiveSylow q.Field q.prime
  have hP : Nat.card P ∣ q.prime ^ (q.exponent * 6) := by
    apply PGroupCardPowerDivisibility.card_dvd_prime_pow_of_le P.isPGroup'
    have hc := CFSGGTwoD4GeckFixedBruhatOrderUpper.originalPositiveSylow_card_le q.Field q.prime
    rw [q.card_field] at hc
    change Nat.card P ≤ (q.prime ^ q.exponent) ^ 6 at hc
    simpa only [pow_mul] using hc
  have houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)) := by
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGGTwoCompleteOuterBudget.typeGTwo_sufficient_outer_budget q hsmall ell hellM
  exact PrimitiveSocleOneFactorTwiceQuadraticSylowTail.genRank_le_ceiling
    D hk q 2 6 (by decide) (CFSGGTwoOriginalGoodSylow.typeGTwo_goodSylowPrime q)
    P hP e.symm.toMonoidHom e.symm.surjective ell hell hfield houter hn

theorem exists_generating_finset (hk : D.factorCount = 1) (q : CFSG.PrimePower)
    (hsmall : q.order ≠ 2) (e : D.Simple ≃* CFSG.Models.G2 q)
    (hn : 1024 ≤ Nat.card X) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U, hU, hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U, hgen, hU.le.trans (genRank_le_ceiling D hk q hsmall e hn)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleGTwoOneFactorOrdinaryTail
