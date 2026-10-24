import SymmetricSubgroupAsymptotics.OriginalBinaryAffineExactChooseDivisorCost
import SymmetricSubgroupAsymptotics.SmallPrimaryLcmEntropy
import SymmetricSubgroupAsymptotics.SmallPrimaryZeroMatchingCeiling
import SymmetricSubgroupAsymptotics.OriginalBinaryAffineSmallPrimaryFrontier
import SymmetricSubgroupAsymptotics.BinaryGeneralLinearSmallPrimeSupport
import Mathlib.Tactic.IntervalCases

/-! Actual small-primary zero-matching steps. The matching coefficient
is the literal binary GL factorization, and unsupported dominant primes
are eliminated by its proved finite support. The remaining witness is
a supported SMALL dominant primary; other top prime factors are not
silently restricted to the GL support. This is not a completed Tracey
theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineSmallZeroMatchingStep
open OriginalAffineBlockCharacteristicHead OriginalBinaryAffineExactChooseDivisorCost
open OriginalBinaryAffineDominantDivisorCost (totalMultiplicity)
open BinaryGeneralLinearMatchingPrimeMultiplicity

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem genRank_le_ceiling_of_small_zero_matching (hp : P.p = 2) (i : block.Points) (q : ℕ)
    (hq : q ∈ (Fintype.card block.Points).primeFactors)
    (hmax : ∀ r ∈ (Fintype.card block.Points).primeFactors,
      r^(Fintype.card block.Points).factorization r ≤ q^(Fintype.card block.Points).factorization q)
    (hM11 : 11 ≤ q^(Fintype.card block.Points).factorization q)
    (hM64 : q^(Fintype.card block.Points).factorization q < 64)
    (hzero : matchingMultiplicity (translationDimension J block P) q = 0)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let t := Fintype.card block.Points
  let d := translationDimension J block P
  let a := t.factorization q
  let M := q^a
  let C : ℝ := totalMultiplicity d
  have ht : 2 ≤ t := by
    simpa only [t,Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have ht0 : t ≠ 0 := by omega
  have hprime := Nat.prime_of_mem_primeFactors hq
  have hd1 : 1 ≤ d := by
    by_contra hh
    have hz : d = 0 := by omega
    have hcard := fibre_card_eq_prime_pow_dimension J block P
    rw [hp,show translationDimension J block P = 0 from hz,pow_zero] at hcard
    have hf := block.degrees_ge_two.1
    omega
  have hC0 : 0 ≤ C := by positivity
  have hC : C ≤ (d : ℝ)^2 := by
    dsimp only [C,totalMultiplicity]
    exact_mod_cast BinaryGeneralLinearTotalPrimeMultiplicity.dimension_add_GL_cardFactors_le_sq d
  have hcost : (MarkedC4.genRank J : ℝ) ≤
      (t : ℝ)*C/(M : ℝ)+MarkedC4.genRank block.Top := by
    have hh := genRank_le_single_divisor_rates J block P hp i q a hprime (Nat.ordProj_dvd t q)
    have hz : matchingMultiplicity d q = 0 := hzero
    calc
      _ ≤ twoDivisorCost d t q a 1 1+MarkedC4.genRank block.Top := hh
      _ = _ := by
        simp only [twoDivisorCost,hz,Nat.cast_zero,zero_mul,zero_add,sub_zero]
        dsimp only [C,M]
        push_cast
        ring
  have htopR : (MarkedC4.genRank block.Top : ℝ) ≤
      (traceyPermutationGeneratorCeiling t : ℝ) := by
    exact_mod_cast (show MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling t by
      simpa only [t,Fintype.card_eq_nat_card] using htop)
  change (MarkedC4.genRank block.Top : ℝ) ≤
    (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) at htopR
  have hentropy := SmallPrimaryLcmEntropy.degree_log_le t M ht0
    (Nat.le_of_lt_succ hM64) hmax
  have hreal := SmallPrimaryZeroMatchingCeiling.aggregate_le M d t hM11 hd1
    (Nat.le_of_dvd (by omega : 0 < t) (Nat.ordProj_dvd t q)) C
      (MarkedC4.genRank J : ℝ) hC0 hC hentropy (hcost.trans (add_le_add le_rfl htopR))
  have hn : n = 2^d*t := by
    calc
      n = Nat.card block.Fibre*Nat.card block.Points := by
        simpa only [Nat.card_fin] using block.degree_product.symm
      _ = 2^d*t := by
        rw [fibre_card_eq_prime_pow_dimension J block P,hp]
        simp only [d,t,Fintype.card_eq_nat_card]
  have hnR : (n : ℝ) = (2 : ℝ)^d*(t : ℝ) := by exact_mod_cast hn
  have hlogn : Real.logb 2 (n : ℝ) = (d : ℝ)+Real.logb 2 (t : ℝ) := by
    rw [hnR,Real.logb_mul (by positivity : (2 : ℝ)^d ≠ 0)
      (by exact_mod_cast ht0),Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one]
  have htarget : (MarkedC4.genRank J : ℝ) ≤ (n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ)) := by
    rw [hlogn,hnR]
    exact hreal
  have hfinal := htarget.trans (Nat.le_ceil ((n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ))))
  change (MarkedC4.genRank J : ℝ) ≤ (traceyPermutationGeneratorCeiling n : ℝ) at hfinal
  exact_mod_cast hfinal

theorem genRank_le_ceiling_of_small_primary_outside_GL_support (hp : P.p = 2)
    (i : block.Points) (q : ℕ) (hq : q ∈ (Fintype.card block.Points).primeFactors)
    (hmax : ∀ r ∈ (Fintype.card block.Points).primeFactors,
      r^(Fintype.card block.Points).factorization r ≤ q^(Fintype.card block.Points).factorization q)
    (hM64 : q^(Fintype.card block.Points).factorization q < 64)
    (hsupport : q ∉ ({2,3,5,7,31} : Finset ℕ))
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  by_cases hd6 : translationDimension J block P ≤ 6
  · have hprime := Nat.prime_of_mem_primeFactors hq
    have hq11 : 11 ≤ q := by
      by_contra hh
      have hq10 : q ≤ 10 := by omega
      interval_cases q <;> norm_num at hprime <;> norm_num at hsupport
    have ha1 : 1 ≤ (Fintype.card block.Points).factorization q := by
      exact (hprime.dvd_iff_one_le_factorization (Nat.mem_primeFactors.mp hq).2.2).mp
        (Nat.dvd_of_mem_primeFactors hq)
    have hqM : q ≤ q^(Fintype.card block.Points).factorization q := by
      simpa only [pow_one] using Nat.pow_le_pow_right hprime.pos ha1
    have hzero := BinaryGeneralLinearSmallPrimeSupport.matchingMultiplicity_eq_zero
      (translationDimension J block P) q hd6 hsupport
    exact genRank_le_ceiling_of_small_zero_matching J block P hp i q hq hmax
      (hq11.trans hqM) hM64 hzero htop
  · exact OriginalBinaryAffineArbitraryTopTail.genRank_le_ceiling_of_dimension_ge_seven
      J block P hp (by omega) i htop

theorem genRank_le_ceiling_or_supported_small_primary (hp : P.p = 2) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n ∨
      ∃ q ∈ (Fintype.card block.Points).primeFactors,
        q ∈ ({2,3,5,7,31} : Finset ℕ) ∧
        (∀ r ∈ (Fintype.card block.Points).primeFactors,
          r^(Fintype.card block.Points).factorization r ≤
            q^(Fintype.card block.Points).factorization q) ∧
        q^(Fintype.card block.Points).factorization q < 64 := by
  obtain hbound | ⟨q,hq,hmax,hsmall⟩ :=
    OriginalBinaryAffineSmallPrimaryFrontier.genRank_le_ceiling_or_small_primary J block P hp i htop
  · exact Or.inl hbound
  · by_cases hsupport : q ∈ ({2,3,5,7,31} : Finset ℕ)
    · exact Or.inr ⟨q,hq,hsupport,hmax,hsmall⟩
    · exact Or.inl (genRank_le_ceiling_of_small_primary_outside_GL_support
        J block P hp i q hq hmax hsmall hsupport htop)

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineSmallZeroMatchingStep
