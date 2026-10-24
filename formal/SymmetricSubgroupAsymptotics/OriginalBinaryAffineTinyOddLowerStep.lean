import SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyComplementFrontier
import SymmetricSubgroupAsymptotics.BinaryGeneralLinearOddSmallStrictMultiplicities
import SymmetricSubgroupAsymptotics.TinyComplementOddSmallDimensionMargins
import SymmetricSubgroupAsymptotics.TinyComplementTernaryDegree
import SymmetricSubgroupAsymptotics.BinaryGeneralLinearSmallExactMultiplicities
import SymmetricSubgroupAsymptotics.CentralBinomialNormalizedAntitone
import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate

/-! The uniform dimension-two/three odd-primary tiny-complement
regimes on the ORIGINAL action. The ternary matching branch uses its
actual prime-to part dividing four; zero matching uses the SAME GL
valuation. The only inductive input is the genuine smaller-top ceiling. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyOddLowerStep
open OriginalAffineBlockCharacteristicHead OriginalBinaryAffineExactChooseDivisorCost
open OriginalBinaryAffineDominantDivisorCost (totalMultiplicity)
open BinaryGeneralLinearMatchingPrimeMultiplicity
open ActualWreathChooseDivisorCapacity

private theorem primaryRate_le_half (q a : ℕ) (hq : 2 ≤ q) (ha : 1 ≤ a) :
    primaryRate q a ≤ (1/2 : ℝ) := by
  have hpred : 1 ≤ q-1 := by omega
  have hprod : 1 ≤ a*(q-1) := by nlinarith only [Nat.mul_le_mul ha hpred]
  have hh := CentralBinomialNormalizedAntitone.normalized_antitone hprod
  unfold primaryRate
  simpa only [show (1 : ℕ)/2 = 0 by decide,Nat.choose_zero_right,Nat.cast_one,pow_one] using hh

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem genRank_le_ceiling_of_tiny_odd_lower (hp : P.p = 2)
    (hd2 : 2 ≤ translationDimension J block P) (hd3 : translationDimension J block P ≤ 3)
    (i : block.Points) (q : ℕ) (hq : q ∈ (Fintype.card block.Points).primeFactors)
    (hq2 : q ≠ 2) (hM7 : 7 ≤ q^(Fintype.card block.Points).factorization q)
    (hM64 : q^(Fintype.card block.Points).factorization q < 64)
    (hother : ∀ r ∈ (Fintype.card block.Points).primeFactors, r ≠ q →
      r^(Fintype.card block.Points).factorization r ≤ 4)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let t := Fintype.card block.Points
  let d := translationDimension J block P
  let a := t.factorization q
  let M := q^a
  let C : ℝ := totalMultiplicity d
  let m : ℝ := matchingMultiplicity d q
  let u := primaryRate q a
  have ht : 2 ≤ t := by
    simpa only [t,Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have ht0 : t ≠ 0 := by omega
  have hprime := Nat.prime_of_mem_primeFactors hq
  have ha : 1 ≤ a :=
    (hprime.dvd_iff_one_le_factorization ht0).mp (Nat.dvd_of_mem_primeFactors hq)
  have hM7' : 7 ≤ M := hM7
  have hM64' : M < 64 := hM64
  have hd2' : 2 ≤ d := hd2
  have hd3' : d ≤ 3 := hd3
  have hm0 : 0 ≤ m := by positivity
  have hmC : m ≤ C := by
    have hh := pair_factorizations_le_cardFactors
      (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))) q (q+1) (by omega)
    have hn : matchingMultiplicity d q ≤ totalMultiplicity d := by
      unfold matchingMultiplicity totalMultiplicity
      split_ifs <;> omega
    dsimp only [m,C]
    exact_mod_cast hn
  have hm1 : m ≤ 1 := by
    have hn : matchingMultiplicity d q ≤ 1 := by
      rw [BinaryGeneralLinearSmallExactMultiplicities.matching_odd_eq d q (by omega) hq2]
      interval_cases d <;> unfold BinaryGeneralLinearSmallExactMultiplicities.smallOddMatching <;>
        split_ifs <;> omega
    dsimp only [m]
    exact_mod_cast hn
  have hu : u ≤ (1/2 : ℝ) := primaryRate_le_half q a hprime.two_le ha
  have hcost : (MarkedC4.genRank J : ℝ) ≤
      (t : ℝ)*(m*u+(C-m)/(M : ℝ))+MarkedC4.genRank block.Top := by
    have hh := genRank_le_single_divisor_rates J block P hp i q a hprime (Nat.ordProj_dvd t q)
    have hhr : (MarkedC4.genRank J : ℝ) ≤ m*(t : ℝ)*u+
        (C-m)*(t : ℝ)/(q : ℝ)^a+MarkedC4.genRank block.Top := by
      simpa only [twoDivisorCost,Nat.cast_one,one_pow,one_div_one,
        min_eq_left (primaryRate_le_one q a)] using hh
    have hqpow : (q : ℝ)^a = (M : ℝ) := by simp only [M,Nat.cast_pow]
    rw [hqpow] at hhr
    convert hhr using 1 <;> ring
  have ht756 : t ≤ 756 := SmallPrimaryTinyComplementDegree.degree_le q t ht0 hM64 hother
  have hentropy : Real.logb 2 (t : ℝ) ≤ 10 := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_upper t 1 10
      (by omega : 0 < t) (by decide) (by simpa only [pow_one] using (show t ≤ 2^10 by omega))
    simpa only [Nat.cast_one,div_one,Nat.cast_ofNat] using hh
  have htopR : (MarkedC4.genRank block.Top : ℝ) ≤ (traceyPermutationGeneratorCeiling t : ℝ) := by
    exact_mod_cast (show MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling t by
      simpa only [t,Fintype.card_eq_nat_card] using htop)
  change (MarkedC4.genRank block.Top : ℝ) ≤
    (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) at htopR
  let L := Real.logb 2 (t : ℝ)
  have hMt : M ≤ t := Nat.le_of_dvd (by omega : 0 < t) (Nat.ordProj_dvd t q)
  have hMR : (7 : ℝ) ≤ M := by exact_mod_cast hM7'
  have hM0 : (0 : ℝ) < M := by linarith only [hMR]
  have hMtR : (M : ℝ) ≤ t := by exact_mod_cast hMt
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hL2 : 2 ≤ L := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_lower t 1 2 (by omega) (by decide)
      (by simpa only [pow_one] using (show 2^2 ≤ t by omega))
    simpa only [Nat.cast_one,div_one,Nat.cast_ofNat,L] using hh
  have hscaled : (m*u+(C-m+1)/(M : ℝ))*Real.sqrt ((d : ℝ)+L)+
      Real.sqrt (1+(d : ℝ)/L) ≤ (2 : ℝ)^d := by
    have hdCases : d = 2 ∨ d = 3 := by omega
    rcases hdCases with hdEq | hdEq
    · have hC4 : C = 4 := by
        dsimp only [C]
        rw [hdEq,BinaryGeneralLinearSmallExactMultiplicities.totalMultiplicity_eq 2 (by decide)]
        norm_num [BinaryGeneralLinearSmallExactMultiplicities.smallTotal]
      by_cases hq3 : q = 3
      · subst q
        have hT4 : t ≤ M*4 := TinyComplementTernaryDegree.degree_le_four_mul_primary t ht0 hother
        have hM27 : M ≤ 27 := TinyComplementTernaryDegree.primary_le_twenty_seven a hM64'
        by_cases hM16 : 16 ≤ M
        · have hT108 : t ≤ 108 := by nlinarith only [hT4,hM27]
          have hL7 : L ≤ 7 := by
            have hh := IntegerLogSquareRootCeilingCertificate.log_upper t 1 7 (by omega) (by decide)
              (by simpa only [pow_one] using (show t ≤ 2^7 by omega))
            simpa only [Nat.cast_one,div_one,Nat.cast_ofNat,L] using hh
          have hL3 : 3 ≤ L := by
            have hh := IntegerLogSquareRootCeilingCertificate.log_lower t 1 3 (by omega) (by decide)
              (by simpa only [pow_one] using (show 2^3 ≤ t by omega))
            simpa only [Nat.cast_one,div_one,Nat.cast_ofNat,L] using hh
          have hh := TinyComplementOddSmallDimensionMargins.two_large_envelope_le
            (M : ℝ) m C u L (by exact_mod_cast hM16) hm0 hm1 hmC hC4.le hu hL3 hL7
          simpa only [hdEq,Nat.cast_ofNat,show (2 : ℝ)^2 = 4 by norm_num] using hh
        · have hM9 : M = 9 := TinyComplementTernaryDegree.short_primary_eq_nine a hM7' (by omega)
          have hT36 : t ≤ 36 := by nlinarith only [hT4,hM9]
          have hL6 : L ≤ 6 := by
            have hh := IntegerLogSquareRootCeilingCertificate.log_upper t 1 6 (by omega) (by decide)
              (by simpa only [pow_one] using (show t ≤ 2^6 by omega))
            simpa only [Nat.cast_one,div_one,Nat.cast_ofNat,L] using hh
          have hL3 : 3 ≤ L := by
            have hh := IntegerLogSquareRootCeilingCertificate.log_lower t 1 3 (by omega) (by decide)
              (by simpa only [pow_one] using (show 2^3 ≤ t by omega))
            simpa only [Nat.cast_one,div_one,Nat.cast_ofNat,L] using hh
          have hh := TinyComplementOddSmallDimensionMargins.two_short_envelope_le
            (M : ℝ) m C u L (by exact_mod_cast hM9.ge) hm0 hm1 hmC hC4.le hu hL3 hL6
          simpa only [hdEq,Nat.cast_ofNat,show (2 : ℝ)^2 = 4 by norm_num] using hh
      · have hmZero : m = 0 := by
          have hn : matchingMultiplicity d q = 0 := by
            rw [hdEq,BinaryGeneralLinearSmallExactMultiplicities.matching_odd_eq 2 q (by decide) hq2]
            unfold BinaryGeneralLinearSmallExactMultiplicities.smallOddMatching
            split_ifs <;> omega
          dsimp only [m]
          exact_mod_cast hn
        have hh := TinyComplementOddSmallDimensionMargins.two_zero_envelope_le
          (M : ℝ) C L hMR (by positivity) hC4.le hL2 hentropy
        simpa only [hdEq,hmZero,zero_mul,sub_zero,zero_add,Nat.cast_ofNat,
          show (2 : ℝ)^2 = 4 by norm_num] using hh
    · have hC8 : C = 8 := by
        dsimp only [C]
        rw [hdEq,BinaryGeneralLinearSmallExactMultiplicities.totalMultiplicity_eq 3 (by decide)]
        norm_num [BinaryGeneralLinearSmallExactMultiplicities.smallTotal]
      have hh := TinyComplementOddSmallDimensionMargins.three_envelope_le
        (M : ℝ) m C u L hMR hm0 hm1 hmC hC8.le hu hL2 hentropy
      simpa only [hdEq,Nat.cast_ofNat,show (2 : ℝ)^3 = 8 by norm_num] using hh
  have hL0 : 0 < L := by linarith only [hL2]
  have hratio : Real.sqrt ((d : ℝ)+L)/Real.sqrt L = Real.sqrt (1+(d : ℝ)/L) := by
    rw [← Real.sqrt_div (by positivity : 0 ≤ (d : ℝ)+L)]
    congr 1
    field_simp [hL0.ne'] <;> ring
  have hceil : (⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) ≤ (t : ℝ)/Real.sqrt L+1 :=
    (Nat.ceil_lt_add_one (div_nonneg htR.le (Real.sqrt_nonneg _))).le
  have hunit : (1 : ℝ) ≤ (t : ℝ)/(M : ℝ) :=
    (le_div_iff₀ hM0).mpr (by simpa only [one_mul] using hMtR)
  have hg : (MarkedC4.genRank J : ℝ) ≤ (t : ℝ)*(m*u+(C-m)/(M : ℝ))+
      (t : ℝ)/Real.sqrt L+(t : ℝ)/(M : ℝ) := by
    have hc := hcost.trans (add_le_add le_rfl htopR)
    change (MarkedC4.genRank J : ℝ) ≤ (t : ℝ)*(m*u+(C-m)/(M : ℝ))+
      (⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) at hc
    linarith only [hc,hceil,hunit]
  have hreal : (MarkedC4.genRank J : ℝ) ≤
      (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+L) := by
    have hs : 0 < Real.sqrt ((d : ℝ)+L) := Real.sqrt_pos.mpr (by positivity)
    rw [← hratio] at hscaled
    apply (le_div_iff₀ hs).mpr
    calc
      (MarkedC4.genRank J : ℝ)*Real.sqrt ((d : ℝ)+L) ≤
          ((t : ℝ)*(m*u+(C-m)/(M : ℝ))+(t : ℝ)/Real.sqrt L+
            (t : ℝ)/(M : ℝ))*Real.sqrt ((d : ℝ)+L) :=
        mul_le_mul_of_nonneg_right hg hs.le
      _ = (t : ℝ)*((m*u+(C-m+1)/(M : ℝ))*Real.sqrt ((d : ℝ)+L)+
          Real.sqrt ((d : ℝ)+L)/Real.sqrt L) := by ring
      _ ≤ (t : ℝ)*(2 : ℝ)^d := mul_le_mul_of_nonneg_left hscaled htR.le
      _ = (2 : ℝ)^d*(t : ℝ) := mul_comm _ _
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

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyOddLowerStep
