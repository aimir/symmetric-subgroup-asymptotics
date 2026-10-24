import SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyComplementFrontier
import SymmetricSubgroupAsymptotics.BinaryGeneralLinearOddSmallStrictMultiplicities
import SymmetricSubgroupAsymptotics.TinyComplementOddCeiling
import SymmetricSubgroupAsymptotics.CentralBinomialNormalizedAntitone
import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate

/-! The higher-dimensional odd-primary tiny-complement regime on the
ORIGINAL action. All local valuations come from the SAME GL order;
the actual prime-to part divides twelve. Only the genuine smaller-top
coarse ceiling remains an inductive hypothesis. No fitting clause,
solvability premise or group catalogue is introduced. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyOddHigherStep
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

theorem genRank_le_ceiling_of_tiny_odd_higher (hp : P.p = 2)
    (hd4 : 4 ≤ translationDimension J block P) (hd6 : translationDimension J block P ≤ 6)
    (i : block.Points) (q : ℕ) (hq : q ∈ (Fintype.card block.Points).primeFactors)
    (hq2 : q ≠ 2) (hM5 : 5 ≤ q^(Fintype.card block.Points).factorization q)
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
  have hM5' : 5 ≤ M := hM5
  have hd4' : 4 ≤ d := hd4
  have hd6' : d ≤ 6 := hd6
  have hm0 : 0 ≤ m := by positivity
  have hmC : m ≤ C := by
    have hh := pair_factorizations_le_cardFactors
      (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))) q (q+1) (by omega)
    have hn : matchingMultiplicity d q ≤ totalMultiplicity d := by
      unfold matchingMultiplicity totalMultiplicity
      split_ifs <;> omega
    dsimp only [m,C]
    exact_mod_cast hn
  have hmA : m ≤ (d : ℝ)-2 := by
    have hn := BinaryGeneralLinearOddSmallStrictMultiplicities.matching_odd_le_sub_two d q hd4' hd6' hq2
    have hR : (matchingMultiplicity d q : ℝ) ≤ ((d-2 : ℕ) : ℝ) := by exact_mod_cast hn
    simpa only [m,Nat.cast_sub (by omega : 2 ≤ d),Nat.cast_ofNat] using hR
  have hC : C ≤ (d : ℝ)^2-2 := by
    have hn := BinaryGeneralLinearOddSmallStrictMultiplicities.total_le_square_sub_two d hd4' hd6'
    have hR : (totalMultiplicity d : ℝ) ≤ ((d^2-2 : ℕ) : ℝ) := by exact_mod_cast hn
    have hdSq : 2 ≤ d^2 := by nlinarith only [Nat.mul_le_mul hd4' hd4']
    simpa only [C,Nat.cast_sub hdSq,Nat.cast_pow,Nat.cast_ofNat] using hR
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
  have hreal := TinyComplementOddCeiling.aggregate_le M d t hM5' hd4'
    (Nat.le_of_dvd (by omega : 0 < t) (Nat.ordProj_dvd t q)) m C u
    (MarkedC4.genRank J : ℝ) hm0 hmA hmC hC hu hentropy (hcost.trans (add_le_add le_rfl htopR))
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

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyOddHigherStep
