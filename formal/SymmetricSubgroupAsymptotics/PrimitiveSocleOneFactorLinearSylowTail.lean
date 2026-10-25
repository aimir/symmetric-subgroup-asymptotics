import SymmetricSubgroupAsymptotics.GoodSylowPrimeOrderOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorPairOrdinaryTail
import SymmetricSubgroupAsymptotics.QuadraticLogOrdinaryGeneratorTail
import SymmetricSubgroupAsymptotics.External.CFSG.Parameters

/-! Actual upper/opposite generation and a selected source-Sylow order
pay a one-factor ordinary tail from a fixed linear ratio between the Sylow exponent and the field-index exponent. The original surjection to the SAME
simple factor is retained, so derived/central-quotient models need no
unproved generating-pair theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorLinearSylowTail
open PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) {A : Type} [Group A] [Finite A]

theorem genRank_le_linear_log (hk : D.factorCount = 1)
    (q : CFSG.PrimePower) (r a : ℕ) (ha : a ≤ 20 * r)
    (hgood : CFSGReduction.GoodSylowPrime A q.prime) (P : Sylow q.prime A)
    (hP : Nat.card P ∣ q.prime ^ (q.exponent * a))
    (f : A →* D.Simple) (hf : Function.Surjective f)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell) (hfield : q.order ^ r ≤ ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    (MarkedC4.genRank G : ℝ) ≤ 21 * Real.logb 2 (Nat.card X : ℝ) + 4 := by
  have hsimple := GoodSylowPrimeOrderOrdinaryGenerators.genRank_le_of_surjective_prime_power
    q.prime (q.exponent * a) hgood P hP f hf
  have hcount : q.exponent * a ≤ 20 * (q.exponent * r) := by
    calc
      q.exponent * a ≤ q.exponent * (20 * r) := Nat.mul_le_mul_left _ ha
      _ = 20 * (q.exponent * r) := by ring
  have hellDegree := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hfield2 : 2 ^ q.exponent ≤ q.order :=
    Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent
  have hpow : 2 ^ (q.exponent * r) ≤ Nat.card X := by
    calc
      _ = (2 ^ q.exponent) ^ r := pow_mul _ _ _
      _ ≤ q.order ^ r := Nat.pow_le_pow_left hfield2 r
      _ ≤ ell := hfield
      _ ≤ Nat.card X := hellDegree
  let L := Real.logb 2 (Nat.card X : ℝ)
  have hdim : ((q.exponent * r : ℕ) : ℝ) ≤ L := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < (2 : ℝ) ^ (q.exponent * r))
      (show (2 : ℝ) ^ (q.exponent * r) ≤ (Nat.card X : ℝ) by exact_mod_cast hpow)
    simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
      mul_one] using hh
  have hsimpleN : MarkedC4.genRank D.Simple ≤ 20 * (q.exponent * r) + 1 :=
    hsimple.trans (Nat.add_le_add_right hcount 1)
  have hsimpleR : (MarkedC4.genRank D.Simple : ℝ) ≤ 20 * L + 1 := by
    have hh : (MarkedC4.genRank D.Simple : ℝ) ≤
        20 * ((q.exponent * r : ℕ) : ℝ) + 1 := by exact_mod_cast hsimpleN
    linarith only [hh, hdim]
  have hOmega := PrimitiveSocleOneFactorPairOrdinaryTail.outerMultiplicity_le_log_degree
    D ell hell houter
  have hrec : (MarkedC4.genRank G : ℝ) ≤ (MarkedC4.genRank D.Simple : ℝ)+
      ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) := by
    exact_mod_cast PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
  change (MarkedC4.genRank G : ℝ) ≤ 21 * L + 4
  linarith only [hrec,hsimpleR,hOmega]

theorem genRank_le_ceiling (hk : D.factorCount = 1)
    (q : CFSG.PrimePower) (r a : ℕ) (ha : a ≤ 20 * r)
    (hgood : CFSGReduction.GoodSylowPrime A q.prime) (P : Sylow q.prime A)
    (hP : Nat.card P ∣ q.prime ^ (q.exponent * a))
    (f : A →* D.Simple) (hf : Function.Surjective f)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell) (hfield : q.order ^ r ≤ ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)))
    (hn : 1024 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  have hh := genRank_le_linear_log D hk q r a ha hgood P hP f hf ell hell hfield houter
  have hL : (10 : ℝ) ≤ Real.logb 2 (Nat.card X : ℝ) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 1024)
      (by exact_mod_cast (show 1024 ≤ Nat.card X by omega) : (1024 : ℝ) ≤ Nat.card X)
    have hlog1024 : Real.logb 2 (1024 : ℝ) = 10 := by
      rw [show (1024 : ℝ) = 2^10 by norm_num, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
      norm_num
    simpa only [hlog1024] using hh
  have hquad : (MarkedC4.genRank G : ℝ) ≤
      2 * (Real.logb 2 (Nat.card X : ℝ))^2 + Real.logb 2 (Nat.card X : ℝ) + 4 := by
    have hL0 := (by norm_num : (0 : ℝ) ≤ 10).trans hL
    have hmul := mul_le_mul_of_nonneg_right hL hL0
    nlinarith only [hh, hmul]
  have hreal := (hquad.trans
    (QuadraticLogOrdinaryGeneratorTail.aggregate_le (Nat.card X) hn)).trans
    (Nat.le_ceil ((Nat.card X : ℝ)/Real.sqrt (Real.logb 2 (Nat.card X : ℝ))))
  change (MarkedC4.genRank G : ℝ) ≤
    (traceyPermutationGeneratorCeiling (Nat.card X) : ℝ) at hreal
  exact_mod_cast hreal

theorem exists_generating_finset (hk : D.factorCount = 1)
    (q : CFSG.PrimePower) (r a : ℕ) (ha : a ≤ 20 * r)
    (hgood : CFSGReduction.GoodSylowPrime A q.prime) (P : Sylow q.prime A)
    (hP : Nat.card P ∣ q.prime ^ (q.exponent * a))
    (f : A →* D.Simple) (hf : Function.Surjective f)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell) (hfield : q.order ^ r ≤ ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)))
    (hn : 1024 ≤ Nat.card X) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U,hgen,hU.le.trans
    (genRank_le_ceiling D hk q r a ha hgood P hP f hf ell hell hfield houter hn)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorLinearSylowTail
