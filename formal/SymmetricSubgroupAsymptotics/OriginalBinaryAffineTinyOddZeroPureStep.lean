import SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyOddZeroNonpureStep
import SymmetricSubgroupAsymptotics.TinyComplementLowerPureCeiling

/-! The pure-top partners of the uniform lower-dimensional zero-matching
intervals. Same-order GL coefficients and the literal primary top are
used directly, with no stronger smaller-action or permutation input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyOddZeroPureStep
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

theorem genRank_le_ceiling_of_pure_odd (hp : P.p = 2)
    (hd1 : 1 ≤ translationDimension J block P) (hd3 : translationDimension J block P ≤ 3)
    (i : block.Points) (q : ℕ) (hq : q ∈ (Fintype.card block.Points).primeFactors)
    (hq2 : q ≠ 2) (hM5 : 5 ≤ q^(Fintype.card block.Points).factorization q)
    (hM9 : q^(Fintype.card block.Points).factorization q ≤ 9)
    (hregime : translationDimension J block P = 1 ∨ q^(Fintype.card block.Points).factorization q = 5)
    (hpure : Fintype.card block.Points = q^(Fintype.card block.Points).factorization q)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let t := Fintype.card block.Points
  let d := translationDimension J block P
  let a := t.factorization q
  let M := q^a
  have hd1' : 1 ≤ d := hd1
  have hd3' : d ≤ 3 := hd3
  have hd' : d = 1 ∨ d = 2 ∨ d = 3 := by omega
  have hM5' : 5 ≤ M := hM5
  have hregime' : d = 1 ∨ M = 5 := hregime
  have hpure' : t = M := hpure
  have hprime := Nat.prime_of_mem_primeFactors hq
  have hmZero : matchingMultiplicity d q = 0 := by
    rw [BinaryGeneralLinearSmallExactMultiplicities.matching_odd_eq d q (by omega) hq2]
    rcases hregime' with hdEq | hMeq
    · norm_num [BinaryGeneralLinearSmallExactMultiplicities.smallOddMatching,hdEq]
    · have hq5 : q = 5 := (Nat.prime_five.pow_eq_iff.mp (show q^a = 5 from hMeq)).1
      norm_num [BinaryGeneralLinearSmallExactMultiplicities.smallOddMatching,hq5,hd3']
  have hcost : MarkedC4.genRank J ≤ totalMultiplicity d+MarkedC4.genRank block.Top := by
    have hh := genRank_le_single_divisor_rates J block P hp i q a hprime (Nat.ordProj_dvd t q)
    have hz : matchingMultiplicity (translationDimension J block P) q = 0 := hmZero
    have hhr : (MarkedC4.genRank J : ℝ) ≤
        (totalMultiplicity d : ℝ)*(t : ℝ)/(q : ℝ)^a+MarkedC4.genRank block.Top := by
      simpa only [twoDivisorCost,hz,Nat.cast_zero,Nat.cast_one,pow_one,one_div_one,zero_mul,zero_add,sub_zero] using hh
    have hqpow : (q : ℝ)^a = (t : ℝ) := by
      exact_mod_cast (show q^a = t from hpure'.symm)
    rw [hqpow] at hhr
    have htR : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
    have hreduce : (totalMultiplicity d : ℝ)*(t : ℝ)/(t : ℝ) = totalMultiplicity d := by
      field_simp [htR]
    rw [hreduce] at hhr
    exact_mod_cast hhr
  have htopNat : MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling t := by
    simpa only [t,Fintype.card_eq_nat_card] using htop
  have hn : n = 2^d*t := by
    calc
      n = Nat.card block.Fibre*Nat.card block.Points := by
        simpa only [Nat.card_fin] using block.degree_product.symm
      _ = 2^d*t := by
        rw [fibre_card_eq_prime_pow_dimension J block P,hp]
        simp only [d,t,Fintype.card_eq_nat_card]
  have hsource := hcost.trans (Nat.add_le_add_left htopNat _)
  rw [BinaryGeneralLinearSmallExactMultiplicities.totalMultiplicity_eq d (by omega)] at hsource
  rcases hd' with hdEq | hdEq | hdEq
  · have hscalar := TinyComplementLowerPureCeiling.one_add_ceiling_le_double t
      (by omega) (show t ≤ 9 from hpure'.trans_le hM9)
    have hsmall : MarkedC4.genRank J ≤ 1+traceyPermutationGeneratorCeiling t := by
      simpa only [hdEq,BinaryGeneralLinearSmallExactMultiplicities.smallTotal] using hsource
    have hn' : n = 2*t := by simpa only [hdEq,pow_one] using hn
    exact (hsmall.trans hscalar).trans_eq (congrArg traceyPermutationGeneratorCeiling hn').symm
  · have hM : M = 5 := hregime'.resolve_left (by omega)
    have ht5 : t = 5 := hpure'.trans hM
    have hsmall : MarkedC4.genRank J ≤ 4+traceyPermutationGeneratorCeiling 5 := by
      simpa only [hdEq,ht5,BinaryGeneralLinearSmallExactMultiplicities.smallTotal] using hsource
    have hn20 : n = 20 := by rw [hdEq,ht5] at hn; norm_num at hn; exact hn
    exact (hsmall.trans TinyComplementLowerPureCeiling.four_add_ceiling_five_le).trans_eq
      (congrArg traceyPermutationGeneratorCeiling hn20).symm
  · have hM : M = 5 := hregime'.resolve_left (by omega)
    have ht5 : t = 5 := hpure'.trans hM
    have htop5 : traceyPermutationGeneratorCeiling 5 ≤ 4 :=
      IntegerLogSquareRootCeilingCertificate.ceil_le_of_square 5 1 2 4
        (by decide) (by decide) (by decide) (by decide) (by decide)
    have hsmall : MarkedC4.genRank J ≤ 12 := by
      have hh : MarkedC4.genRank J ≤ 8+traceyPermutationGeneratorCeiling 5 := by
        simpa only [hdEq,ht5,BinaryGeneralLinearSmallExactMultiplicities.smallTotal] using hsource
      omega
    have htarget : 12 ≤ traceyPermutationGeneratorCeiling 40 :=
      IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 40 1 6 12
        (by decide) (by decide) (by decide) (by decide) (by decide)
    have hn40 : n = 40 := by rw [hdEq,ht5] at hn; norm_num at hn; exact hn
    exact (hsmall.trans htarget).trans_eq (congrArg traceyPermutationGeneratorCeiling hn40).symm

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyOddZeroPureStep
