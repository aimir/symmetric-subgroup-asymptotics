import SymmetricSubgroupAsymptotics.CFSGUnitaryActualSylowOrdinaryHead
import SymmetricSubgroupAsymptotics.CFSGUnitaryCoprimeOuterCardinality
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoOuterGcdBound
import SymmetricSubgroupAsymptotics.UnitaryBelowThirtyTwoFieldRankParameters
import SymmetricSubgroupAsymptotics.SmallSharpOuterPairNumerics

/-! The SAME original model supplies both ordinary head and outer
multiplicity in the bounded unitary parameters. Five parameter states
have uniform proved cost profiles; the binary rank-three state remains
explicit, rather than being declared nonsimple or two-generated. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGUnitarySmallActualOrdinaryProfiles
open PrimitiveSocleRawStructure CFSGTwistedAUnitaryCoordinates

private theorem omega_le {T : Type} [Group T] [Finite T] (k N : ℕ)
    (hN : Nat.card (Outer T) ≤ N) (hpow : N < 2^(k+1)) :
    ArithmeticFunction.cardFactors (Nat.card (Outer T)) ≤ k :=
  SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow _ k Nat.card_pos (hN.trans_lt hpow)

theorem profiles (r : ℕ) (q : CFSG.PrimePower) (hr : 2 ≤ r)
    (hs : r = 2 → q.order ≠ 2) [Finite (CFSG.Models.TwistedA r q)]
    [IsSimpleGroup (CFSG.Models.TwistedA r q)]
    (hn : ¬ IsMulCommutative (CFSG.Models.TwistedA r q)) (hsmall : q.order^r < 32) :
    ((9 ≤ q.order^r ∧ MarkedC4.genRank (CFSG.Models.TwistedA r q) ≤ 4 ∧
        ArithmeticFunction.cardFactors (Nat.card (Outer (CFSG.Models.TwistedA r q))) ≤ 1) ∨
      (16 ≤ q.order^r ∧ MarkedC4.genRank (CFSG.Models.TwistedA r q) ≤ 7 ∧
        ArithmeticFunction.cardFactors (Nat.card (Outer (CFSG.Models.TwistedA r q))) ≤ 2) ∨
      (24 ≤ q.order^r ∧ MarkedC4.genRank (CFSG.Models.TwistedA r q) ≤ 8 ∧
        ArithmeticFunction.cardFactors (Nat.card (Outer (CFSG.Models.TwistedA r q))) ≤ 3) ∨
      (16 ≤ q.order^r ∧ MarkedC4.genRank (CFSG.Models.TwistedA r q) ≤ 11 ∧
        ArithmeticFunction.cardFactors (Nat.card (Outer (CFSG.Models.TwistedA r q))) ≤ 1)) ∨
      (r = 3 ∧ q.order = 2) := by
  have hparam := UnitaryBelowThirtyTwoFieldRankParameters.parameters r q.order hr
    (CFSGTwistedAQuadraticTrace.order_two_le q) hs hsmall
  rcases hparam with ⟨rfl,hq | hq | hq⟩ | ⟨rfl,hq | hq⟩ | ⟨rfl,hq⟩
  · have he := ClassicalClassEquationCapacity.exponent_eq_one_of_prime_order q (by rw [hq]; decide)
    have hh := CFSGUnitaryActualSylowOrdinaryHead.genRank_le 2 q (by decide) hs
    have hout := twistedA_rankTwo_outer_order_le_gcd_exponent q (by omega)
    have hh4 : MarkedC4.genRank (CFSG.Models.TwistedA 2 q) ≤ 4 := by simpa only [he] using hh
    have hout2 : Nat.card (Outer (CFSG.Models.TwistedA 2 q)) ≤ 2 := by
      norm_num [hq,he] at hout
      exact hout
    exact Or.inl (Or.inl ⟨by norm_num [hq],hh4,omega_le 1 2 hout2 (by decide)⟩)
  · have he : q.exponent = 2 := (Nat.Prime.pow_inj' q.prime_isPrime Nat.prime_two
      q.exponent_pos.ne' (by decide : (2 : ℕ) ≠ 0)
      (show q.prime^q.exponent = 2^2 from hq)).2
    have hh := CFSGUnitaryActualSylowOrdinaryHead.genRank_le 2 q (by decide) hs
    have hout := twistedA_rankTwo_outer_order_le_gcd_exponent q (by omega)
    have hh7 : MarkedC4.genRank (CFSG.Models.TwistedA 2 q) ≤ 7 := by simpa only [he] using hh
    have hout4 : Nat.card (Outer (CFSG.Models.TwistedA 2 q)) ≤ 4 := by
      norm_num [hq,he] at hout
      exact hout
    exact Or.inl (Or.inr (Or.inl ⟨by norm_num [hq],hh7,omega_le 2 4 hout4 (by decide)⟩))
  · have he := ClassicalClassEquationCapacity.exponent_eq_one_of_prime_order q (by rw [hq]; decide)
    have hh := CFSGUnitaryActualSylowOrdinaryHead.genRank_le 2 q (by decide) hs
    have hout := twistedA_rankTwo_outer_order_le_gcd_exponent q (by omega)
    have hh4 : MarkedC4.genRank (CFSG.Models.TwistedA 2 q) ≤ 4 := by simpa only [he] using hh
    have hout6 : Nat.card (Outer (CFSG.Models.TwistedA 2 q)) ≤ 6 := by
      norm_num [hq,he] at hout
      exact hout
    exact Or.inl (Or.inr (Or.inr (Or.inl ⟨by norm_num [hq],hh4.trans (by decide),
      (omega_le 2 6 hout6 (by decide)).trans (by decide)⟩)))
  · exact Or.inr ⟨rfl,hq⟩
  · have he := ClassicalClassEquationCapacity.exponent_eq_one_of_prime_order q (by rw [hq]; decide)
    have hh := CFSGUnitaryActualSylowOrdinaryHead.genRank_le 3 q (by decide) hs
    have hout := twistedA_higher_outer_order_le q 0 hn
    have hh7 : MarkedC4.genRank (CFSG.Models.TwistedA 3 q) ≤ 7 := by simpa only [he] using hh
    have hout8 : Nat.card (Outer (CFSG.Models.TwistedA 3 q)) ≤ 8 := by
      norm_num [he] at hout
      exact hout
    exact Or.inl (Or.inr (Or.inr (Or.inl ⟨by norm_num [hq],hh7.trans (by decide),
      omega_le 3 8 hout8 (by decide)⟩)))
  · have he := ClassicalClassEquationCapacity.exponent_eq_one_of_prime_order q (by rw [hq]; decide)
    have hh := CFSGUnitaryActualSylowOrdinaryHead.genRank_le 4 q (by decide) hs
    have hh11 : MarkedC4.genRank (CFSG.Models.TwistedA 4 q) ≤ 11 := by simpa only [he] using hh
    have hout2 := CFSGUnitaryCoprimeOuterCardinality.binary_rank_three_or_four_outer_card_le_two
      q hq 1 (Or.inr rfl) hn
    exact Or.inl (Or.inr (Or.inr (Or.inr ⟨by norm_num [hq],hh11,omega_le 1 2 hout2 (by decide)⟩)))

end SymmetricSubgroupAsymptotics.CFSGUnitarySmallActualOrdinaryProfiles
