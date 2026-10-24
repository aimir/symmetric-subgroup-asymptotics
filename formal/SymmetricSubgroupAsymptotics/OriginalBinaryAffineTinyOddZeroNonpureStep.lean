import SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyOddLowerStep
import SymmetricSubgroupAsymptotics.TinyComplementOddZeroSmallCeiling

/-! Nonpure zero-matching lower-dimensional odd primaries on the
original action. Exact GL coefficients force zero matching in dimension
one, or for the actual primary five in dimensions two/three. The true
complementary divisor supplies the half-unit rounding improvement. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyOddZeroNonpureStep
open OriginalAffineBlockCharacteristicHead OriginalBinaryAffineExactChooseDivisorCost
open OriginalBinaryAffineDominantDivisorCost (totalMultiplicity)
open BinaryGeneralLinearMatchingPrimeMultiplicity
open ActualWreathChooseDivisorCapacity

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem genRank_le_ceiling_of_nonpure_odd (hp : P.p = 2)
    (hd1 : 1 ≤ translationDimension J block P) (hd3 : translationDimension J block P ≤ 3)
    (i : block.Points) (q : ℕ) (hq : q ∈ (Fintype.card block.Points).primeFactors)
    (hq2 : q ≠ 2) (hM5 : 5 ≤ q^(Fintype.card block.Points).factorization q)
    (hM9 : q^(Fintype.card block.Points).factorization q ≤ 9)
    (hregime : translationDimension J block P = 1 ∨ q^(Fintype.card block.Points).factorization q = 5)
    (hnonpure : 2*q^(Fintype.card block.Points).factorization q ≤ Fintype.card block.Points)
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
  have hd1' : 1 ≤ d := hd1
  have hd3' : d ≤ 3 := hd3
  have hd' : d = 1 ∨ d = 2 ∨ d = 3 := by omega
  have hM5' : 5 ≤ M := hM5
  have hM9' : M ≤ 9 := hM9
  have hregime' : d = 1 ∨ M = 5 := hregime
  have hnonpure' : 2*M ≤ t := hnonpure
  have ht0 : t ≠ 0 := by omega
  have hprime := Nat.prime_of_mem_primeFactors hq
  have hmZero : matchingMultiplicity d q = 0 := by
    rw [BinaryGeneralLinearSmallExactMultiplicities.matching_odd_eq d q (by omega) hq2]
    rcases hregime' with hdEq | hMeq
    · norm_num [BinaryGeneralLinearSmallExactMultiplicities.smallOddMatching,hdEq]
    · have hq5 : q = 5 := (Nat.prime_five.pow_eq_iff.mp (show q^a = 5 from hMeq)).1
      norm_num [BinaryGeneralLinearSmallExactMultiplicities.smallOddMatching,hq5,hd3']
  have hC : C ≤ if d = 1 then 1 else (2 : ℝ)^d := by
    dsimp only [C]
    rw [BinaryGeneralLinearSmallExactMultiplicities.totalMultiplicity_eq d (by omega)]
    rcases hd' with hdEq | hdEq | hdEq <;>
      norm_num [hdEq,BinaryGeneralLinearSmallExactMultiplicities.smallTotal]
  have hT12 : t ≤ M*12 := by
    have hk := Nat.le_of_dvd (by decide : 0 < 12)
      (SmallPrimaryTinyComplementDegree.otherPart_dvd_twelve q t ht0 hother)
    have hh := Nat.mul_le_mul_left (q^t.factorization q) hk
    rw [Nat.ordProj_mul_ordCompl_eq_self] at hh
    exact hh
  have ht128 : t ≤ 128 := by nlinarith only [hT12,hM9']
  have hsmall : d = 1 ∨ t ≤ 64 := by
    rcases hregime' with hdEq | hMeq
    · exact Or.inl hdEq
    · exact Or.inr (by nlinarith only [hT12,hMeq])
  have hcost : (MarkedC4.genRank J : ℝ) ≤
      (t : ℝ)*C/(M : ℝ)+MarkedC4.genRank block.Top := by
    have hh := genRank_le_single_divisor_rates J block P hp i q a hprime (Nat.ordProj_dvd t q)
    have hz : matchingMultiplicity (translationDimension J block P) q = 0 := hmZero
    have hhr : (MarkedC4.genRank J : ℝ) ≤
        (totalMultiplicity d : ℝ)*(t : ℝ)/(q : ℝ)^a+MarkedC4.genRank block.Top := by
      simpa only [twoDivisorCost,hz,Nat.cast_zero,Nat.cast_one,pow_one,one_div_one,zero_mul,zero_add,sub_zero] using hh
    have hqpow : (q : ℝ)^a = (M : ℝ) := by simp only [M,Nat.cast_pow]
    simpa only [hqpow,C,mul_comm] using hhr
  have htopR : (MarkedC4.genRank block.Top : ℝ) ≤ (traceyPermutationGeneratorCeiling t : ℝ) := by
    exact_mod_cast (show MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling t by
      simpa only [t,Fintype.card_eq_nat_card] using htop)
  change (MarkedC4.genRank block.Top : ℝ) ≤
    (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) at htopR
  have hreal := TinyComplementOddZeroSmallCeiling.aggregate_le M d t hM5' hnonpure' hd'
    ht128 hsmall C (MarkedC4.genRank J : ℝ) (by positivity) hC
    (hcost.trans (add_le_add le_rfl htopR))
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

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyOddZeroNonpureStep
