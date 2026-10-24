import SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyBinaryHigherStep
import SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyBinaryLowerStep
import SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyTernaryLowerStep
import SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyOddZeroPureStep
import SymmetricSubgroupAsymptotics.TinyComplementPrimaryExhaustion

/-! Exhaustion of the literal binary affine block component on an
arbitrary actual top action. Every branch retains the original group,
point degree and same chief-order coefficients. The only generation
input is the genuine strictly-smaller top's coarse ceiling. No global
Tracey/MN conclusion, solvability or simple two-generation is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineArbitraryTopOrdinaryStep
open OriginalAffineBlockCharacteristicHead BinaryGeneralLinearMatchingPrimeMultiplicity

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

private theorem small_odd_zero (hp : P.p = 2)
    (hd1 : 1 ≤ translationDimension J block P) (hd3 : translationDimension J block P ≤ 3)
    (i : block.Points) (q : ℕ) (hq : q ∈ (Fintype.card block.Points).primeFactors)
    (hq2 : q ≠ 2) (hM5 : 5 ≤ q^(Fintype.card block.Points).factorization q)
    (hM9 : q^(Fintype.card block.Points).factorization q ≤ 9)
    (hregime : translationDimension J block P = 1 ∨ q^(Fintype.card block.Points).factorization q = 5)
    (hother : ∀ r ∈ (Fintype.card block.Points).primeFactors, r ≠ q →
      r^(Fintype.card block.Points).factorization r ≤ 4)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let t := Fintype.card block.Points
  let M := q^t.factorization q
  by_cases hpure : t = M
  · exact OriginalBinaryAffineTinyOddZeroPureStep.genRank_le_ceiling_of_pure_odd
      J block P hp hd1 hd3 i q hq hq2 hM5 hM9 hregime hpure htop
  have hdiv : M ∣ t := Nat.ordProj_dvd t q
  obtain ⟨k,hk⟩ := hdiv
  have ht0 : t ≠ 0 := Fintype.card_ne_zero
  have hk2 : 2 ≤ k := by
    have hk0 : k ≠ 0 := by
      intro hz
      rw [hz,mul_zero] at hk
      exact ht0 hk
    by_contra hh
    have hk1 : k = 1 := by omega
    apply hpure
    simpa only [hk1,mul_one] using hk
  have hnonpure : 2*M ≤ t := by
    rw [hk]
    simpa only [Nat.mul_comm 2 M] using Nat.mul_le_mul_left M hk2
  exact OriginalBinaryAffineTinyOddZeroNonpureStep.genRank_le_ceiling_of_nonpure_odd
    J block P hp hd1 hd3 i q hq hq2 hM5 hM9 hregime hnonpure hother htop

theorem genRank_le_ceiling (hp : P.p = 2) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  obtain hbound | ⟨q,hq,hsupport,hmax,hM64,hd6,hother,k,hk1,hk12,hcop,hshape,ht756⟩ :=
    OriginalBinaryAffineTinyComplementFrontier.genRank_le_ceiling_or_actual_tiny_data
      J block P hp i htop
  · exact hbound
  let t := Fintype.card block.Points
  let d := translationDimension J block P
  let a := t.factorization q
  let M := q^a
  have ht0 : t ≠ 0 := Fintype.card_ne_zero
  have hd6' : d ≤ 6 := hd6
  have hM64' : M < 64 := hM64
  have hd1 : 1 ≤ d := by
    by_contra hh
    have hd0 : d = 0 := by omega
    have hcard := fibre_card_eq_prime_pow_dimension J block P
    rw [hp,show translationDimension J block P = 0 from hd0,pow_zero] at hcard
    have hf := block.degrees_ge_two.1
    omega
  have hprime := Nat.prime_of_mem_primeFactors hq
  have ha1 : 1 ≤ a :=
    (hprime.dvd_iff_one_le_factorization ht0).mp (Nat.dvd_of_mem_primeFactors hq)
  by_cases hq2 : q = 2
  · subst q
    have hother3 := TinyComplementPrimaryExhaustion.other_odd_powers_le_three t hother
    have ha5 := TinyComplementPrimaryExhaustion.binary_small_exponent a hM64'
    rcases BinarySmallThreeComplementDegree.eq_binary_or_three_mul t ht0 hother3 with hbinary | hthree
    · exact OriginalBinaryAffinePrimeMultiplicitySteps.genRank_le_ceiling
        J block P hp a ha1 hbinary i htop
    have hdiv3 : 3 ∣ t := by rw [hthree]; exact dvd_mul_right 3 (2^a)
    have hmem3 : 3 ∈ t.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three,hdiv3,ht0⟩
    have hfac3 : 1 ≤ t.factorization 3 :=
      (Nat.prime_three.dvd_iff_one_le_factorization ht0).mp hdiv3
    have hthreePrimary : 3 ≤ 3^t.factorization 3 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 3) hfac3
    have hM3 : 3 ≤ 2^a := hthreePrimary.trans (hmax 3 hmem3)
    have ha2 : 2 ≤ a := by
      by_contra hh
      have haEq : a = 1 := by omega
      norm_num only [haEq,pow_one] at hM3
    by_cases hd2 : d = 2
    · exact OriginalFourPointSharedSmallBinaryTopStep.genRank_le_ceiling_of_three_mul_binary
        J block P hp hd2 i a (by omega) ha5 hthree htop
    by_cases hd4 : 4 ≤ d
    · exact OriginalBinaryAffineTinyBinaryHigherStep.genRank_le_ceiling_of_three_mul_binary
        J block P hp hd4 hd6 i a ha2 ha5 hthree htop
    · exact OriginalBinaryAffineTinyBinaryLowerStep.genRank_le_ceiling_of_three_mul_binary
        J block P hp (show d = 1 ∨ d = 3 by omega) i a ha2 ha5 hthree htop
  · rcases TinyComplementPrimaryExhaustion.odd_primary_cases q a hprime hq2 ha1 with hM3 | hM5 | hM7
    · have hq3 : q = 3 := (Nat.prime_three.pow_eq_iff.mp hM3).1
      subst q
      have hprimary : 3^t.factorization 3 = 3 := hM3
      have hother3 : ∀ r ∈ t.primeFactors, r ≠ 3 → r^t.factorization r ≤ 3 := by
        intro r hr _
        exact (hmax r hr).trans_eq hprimary
      by_cases hd3 : d ≤ 3
      · exact OriginalBinaryAffineTinyTernaryLowerStep.genRank_le_ceiling_of_dominant_three
          J block P hp hd1 hd3 i hprimary hother3 htop
      · exact OriginalBinaryAffineTinyTernaryHigherStep.genRank_le_ceiling_of_dominant_three
          J block P hp (show 4 ≤ d by omega) hd6 i hprimary hother3 htop
    · by_cases hd4 : 4 ≤ d
      · exact OriginalBinaryAffineTinyOddHigherStep.genRank_le_ceiling_of_tiny_odd_higher
          J block P hp hd4 hd6 i q hq hq2 (show 5 ≤ q^a by omega) hM64 hother htop
      · exact small_odd_zero J block P hp hd1 (show d ≤ 3 by omega) i q hq hq2
          (show 5 ≤ q^a by omega) (show q^a ≤ 9 by omega) (Or.inr hM5) hother htop
    · by_cases hd4 : 4 ≤ d
      · exact OriginalBinaryAffineTinyOddHigherStep.genRank_le_ceiling_of_tiny_odd_higher
          J block P hp hd4 hd6 i q hq hq2 (show 5 ≤ q^a by omega) hM64 hother htop
      by_cases hd2 : 2 ≤ d
      · exact OriginalBinaryAffineTinyOddLowerStep.genRank_le_ceiling_of_tiny_odd_lower
          J block P hp hd2 (show d ≤ 3 by omega) i q hq hq2 hM7 hM64 hother htop
      have hdEq : d = 1 := by omega
      by_cases hM11 : 11 ≤ M
      · have hzero : matchingMultiplicity (translationDimension J block P) q = 0 := by
          rw [show translationDimension J block P = 1 from hdEq,
            BinaryGeneralLinearSmallExactMultiplicities.matching_odd_eq 1 q (by decide) hq2]
          norm_num [BinaryGeneralLinearSmallExactMultiplicities.smallOddMatching]
        exact OriginalBinaryAffineSmallZeroMatchingStep.genRank_le_ceiling_of_small_zero_matching
          J block P hp i q hq hmax hM11 hM64 hzero htop
      · have hM9 : M ≤ 9 := TinyComplementPrimaryExhaustion.odd_primary_le_nine q a hprime hq2 (show q^a < 11 by change M < 11; omega)
        exact small_odd_zero J block P hp hd1 (show d ≤ 3 by omega) i q hq hq2
          (show 5 ≤ q^a by omega) hM9 (Or.inl hdEq) hother htop

theorem exists_generating_finset (hp : P.p = 2) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧
      S.card ≤ traceyPermutationGeneratorCeiling n := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨S,hgen,hS.le.trans (genRank_le_ceiling J block P hp i htop)⟩

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineArbitraryTopOrdinaryStep
