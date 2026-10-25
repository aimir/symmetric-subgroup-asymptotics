import SymmetricSubgroupAsymptotics.UnitaryBoundedPrimitiveOrdinaryNumerics
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoFrattiniOrdinaryHead
import SymmetricSubgroupAsymptotics.CFSGUnitaryBinaryRankFourOrdinaryHead
import SymmetricSubgroupAsymptotics.CFSGUnitaryUpperProductOrdinaryHeads
import SymmetricSubgroupAsymptotics.CFSGUnitarySmallActualOrdinaryProfiles

/-! Literal original-model ordinary plus outer costs for bounded unitary
one-factor actions. Three scalar field-rank product bands and the genuine
small parameter reduction suffice. The hard states use actual Frattini
heads; no action catalogue or desired aggregate premise is supplied. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGUnitaryBoundedOrdinaryProfiles
open PrimitiveSocleRawStructure CFSGTwistedAUnitaryCoordinates
open UnitaryBoundedPrimitiveOrdinaryNumerics

private theorem outer_card_bound (r : ℕ) (q : CFSG.PrimePower) (hr : 2 ≤ r)
    (hs : r = 2 → q.order ≠ 2) [IsSimpleGroup (CFSG.Models.TwistedA r q)]
    (hn : ¬ IsMulCommutative (CFSG.Models.TwistedA r q)) :
    Nat.card (Outer (CFSG.Models.TwistedA r q)) ≤ 2*q.exponent*(r+1) := by
  by_cases hh : r = 2
  · subst r
    have hq := CFSGTwistedAQuadraticTrace.order_two_le q
    have hout := twistedA_rankTwo_outer_order_le_gcd_exponent q (by have := hs rfl; omega)
    have hg : (q.order+1).gcd 3 ≤ 3 := Nat.gcd_le_right _ (by decide)
    nlinarith
  · obtain ⟨s,rfl⟩ : ∃ s : ℕ, r = s+3 := ⟨r-3,by omega⟩
    exact twistedA_higher_outer_order_le q s hn

private theorem omega_bound {T : Type} [Group T] [Finite T] (k N : ℕ)
    (hN : Nat.card (Outer T) ≤ N) (hpow : N < 2^(k+1)) :
    ArithmeticFunction.cardFactors (Nat.card (Outer T)) ≤ k :=
  SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow _ k Nat.card_pos (hN.trans_lt hpow)

theorem model_cost_le_ceiling (r : ℕ) (q : CFSG.PrimePower) (hr : 2 ≤ r)
    (hs : r = 2 → q.order ≠ 2) [Finite (CFSG.Models.TwistedA r q)]
    [IsSimpleGroup (CFSG.Models.TwistedA r q)]
    (hn : ¬ IsMulCommutative (CFSG.Models.TwistedA r q))
    (n : ℕ) (hdegree : q.order^r ≤ n) (hsmall : n < 1024) :
    MarkedC4.genRank (CFSG.Models.TwistedA r q)+
      ArithmeticFunction.cardFactors (Nat.card (Outer (CFSG.Models.TwistedA r q))) ≤
        traceyPermutationGeneratorCeiling n := by
  have hraw := CFSGUnitaryActualSylowOrdinaryHead.genRank_le r q hr hs
  have hout := outer_card_bound r q hr hs hn
  have hf : 1 ≤ q.exponent := q.exponent_pos
  by_cases h32 : 32 ≤ n
  · by_cases h64 : 64 ≤ n
    · by_cases h128 : 128 ≤ n
      · by_cases h256 : 256 ≤ n
        · have hp := product_bound q.prime q.exponent r n 9 q.prime_isPrime.two_le hdegree hsmall
          have hh := head_bound q.exponent r 9 hf (by omega) hp
          have ho := hout.trans (outer_size_bound q.exponent r 9 hf (by omega) hp)
          have hom := omega_bound 5 36 ho (by decide)
          exact band_ceiling n _ (Or.inr (Or.inr (Or.inr ⟨h256,by omega⟩)))
        · have hp := product_bound q.prime q.exponent r n 7 q.prime_isPrime.two_le hdegree (by omega)
          have hh := head_bound q.exponent r 7 hf (by omega) hp
          have ho := hout.trans (outer_size_bound q.exponent r 7 hf (by omega) hp)
          have hom := omega_bound 4 28 ho (by decide)
          exact band_ceiling n _ (Or.inr (Or.inr (Or.inl ⟨h128,by omega⟩)))
      · have hp := product_bound q.prime q.exponent r n 6 q.prime_isPrime.two_le hdegree (by omega)
        have hh := head_bound q.exponent r 6 hf (by omega) hp
        have ho := hout.trans (outer_size_bound q.exponent r 6 hf (by omega) hp)
        have hom := omega_bound 4 24 ho (by decide)
        exact band_ceiling n _ (Or.inr (Or.inl ⟨h64,by omega⟩))
    · have hp := product_bound q.prime q.exponent r n 5 q.prime_isPrime.two_le hdegree (by omega)
      by_cases hr4 : r ≤ 4
      · have hh := small_product_head q.exponent r hf hr hr4 hp
        have ho := hout.trans (outer_size_bound q.exponent r 5 hf (by omega) hp)
        have hom := omega_bound 4 20 ho (by decide)
        exact band_ceiling n _ (Or.inl ⟨h32,by omega⟩)
      · have hrle : r ≤ 5 := (Nat.le_mul_of_pos_left r hf).trans hp
        have hr5 : r = 5 := by omega
        have he : q.exponent = 1 := by rw [hr5] at hp; omega
        subst r
        have hq2 : q.order = 2 := by
          have hq := CFSGTwistedAQuadraticTrace.order_two_le q
          by_contra hh
          have hpow := Nat.pow_le_pow_left (show 3 ≤ q.order by omega) 5
          norm_num at hpow
          omega
        have hhead := CFSGUnitaryUpperProductOrdinaryHeads.binary_rank_five_model_le_twelve q hq2
        have ho : Nat.card (Outer (CFSG.Models.TwistedA 5 q)) ≤ 12 := by simpa only [he] using hout
        have hom := omega_bound 3 12 ho (by decide)
        exact band_ceiling n _ (Or.inl ⟨h32,by omega⟩)
  have hparam := UnitaryBelowThirtyTwoFieldRankParameters.parameters r q.order hr
    (CFSGTwistedAQuadraticTrace.order_two_le q) hs (hdegree.trans_lt (by omega))
  rcases hparam with ⟨rfl,hq | hq | hq⟩ | ⟨rfl,hq | hq⟩ | ⟨rfl,hq⟩
  · have he := ClassicalClassEquationCapacity.exponent_eq_one_of_prime_order q (by rw [hq]; decide)
    have hhead := CFSGUnitaryRankTwoFrattiniOrdinaryHead.model_genRank_le q (by omega)
    have ho : Nat.card (Outer (CFSG.Models.TwistedA 2 q)) ≤ 2 := by
      have hh := twistedA_rankTwo_outer_order_le_gcd_exponent q (by omega)
      norm_num [hq,he] at hh
      exact hh
    have hom := omega_bound 1 2 ho (by decide)
    have hH : MarkedC4.genRank (CFSG.Models.TwistedA 2 q) ≤ 3 := by simpa only [he] using hhead
    exact small_profile_ceiling n _ (Or.inl ⟨by norm_num [hq] at hdegree; omega,by omega⟩)
  · have he : q.exponent = 2 := (Nat.Prime.pow_inj' q.prime_isPrime Nat.prime_two
      q.exponent_pos.ne' (by decide : (2 : ℕ) ≠ 0)
      (show q.prime^q.exponent = 2^2 from hq)).2
    have hhead := CFSGUnitaryRankTwoFrattiniOrdinaryHead.model_genRank_le q (by omega)
    have ho : Nat.card (Outer (CFSG.Models.TwistedA 2 q)) ≤ 4 := by
      have hh := twistedA_rankTwo_outer_order_le_gcd_exponent q (by omega)
      norm_num [hq,he] at hh
      exact hh
    have hom := omega_bound 2 4 ho (by decide)
    have hH : MarkedC4.genRank (CFSG.Models.TwistedA 2 q) ≤ 5 := by simpa only [he] using hhead
    exact small_profile_ceiling n _ (Or.inr (Or.inl ⟨by norm_num [hq] at hdegree; omega,by omega⟩))
  · have he := ClassicalClassEquationCapacity.exponent_eq_one_of_prime_order q (by rw [hq]; decide)
    have hhead := CFSGUnitaryRankTwoFrattiniOrdinaryHead.model_genRank_le q (by omega)
    have ho : Nat.card (Outer (CFSG.Models.TwistedA 2 q)) ≤ 6 := by
      have hh := twistedA_rankTwo_outer_order_le_gcd_exponent q (by omega)
      norm_num [hq,he] at hh
      exact hh
    have hom := omega_bound 2 6 ho (by decide)
    have hH : MarkedC4.genRank (CFSG.Models.TwistedA 2 q) ≤ 3 := by simpa only [he] using hhead
    exact small_profile_ceiling n _ (Or.inl ⟨by norm_num [hq] at hdegree; omega,by omega⟩)
  · have hhead := CFSGUnitaryBinaryRankThreeFrattiniHead.model_genRank_le_four q hq
    have ho := CFSGUnitaryCoprimeOuterCardinality.binary_rank_three_or_four_outer_card_le_two
      q hq 0 (Or.inl rfl) hn
    have hom := omega_bound 1 2 ho (by decide)
    change ArithmeticFunction.cardFactors (Nat.card (Outer (CFSG.Models.TwistedA 3 q))) ≤ 1 at hom
    have hn8 : 8 ≤ n := by norm_num [hq] at hdegree; exact hdegree
    exact (show MarkedC4.genRank (CFSG.Models.TwistedA 3 q)+
      ArithmeticFunction.cardFactors (Nat.card (Outer (CFSG.Models.TwistedA 3 q))) ≤ 5 by omega).trans
        (SmallSharpOuterPairNumerics.five_le_ceiling n (by omega))
  · have he := ClassicalClassEquationCapacity.exponent_eq_one_of_prime_order q (by rw [hq]; decide)
    have hH : MarkedC4.genRank (CFSG.Models.TwistedA 3 q) ≤ 7 := by simpa only [he] using hraw
    have ho : Nat.card (Outer (CFSG.Models.TwistedA 3 q)) ≤ 8 := by simpa only [he] using hout
    have hom := omega_bound 3 8 ho (by decide)
    exact small_profile_ceiling n _ (Or.inr (Or.inr ⟨by norm_num [hq] at hdegree; omega,by omega⟩))
  · have hhead := CFSGUnitaryBinaryRankFourOrdinaryHead.model_genRank_le_seven q hq
    have ho := CFSGUnitaryCoprimeOuterCardinality.binary_rank_three_or_four_outer_card_le_two
      q hq 1 (Or.inr rfl) hn
    have hom := omega_bound 1 2 ho (by decide)
    change ArithmeticFunction.cardFactors (Nat.card (Outer (CFSG.Models.TwistedA 4 q))) ≤ 1 at hom
    exact small_profile_ceiling n _ (Or.inr (Or.inl ⟨by norm_num [hq] at hdegree; omega,by omega⟩))

end SymmetricSubgroupAsymptotics.CFSGUnitaryBoundedOrdinaryProfiles
