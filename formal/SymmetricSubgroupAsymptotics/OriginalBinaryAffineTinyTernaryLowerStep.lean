import SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyTernaryHigherStep
import SymmetricSubgroupAsymptotics.OriginalFourPointSharedSmallBinaryTopStep
import SymmetricSubgroupAsymptotics.BinaryGeneralLinearSmallExactMultiplicities
import SymmetricSubgroupAsymptotics.TinyTernaryLowerCeilingCertificates

/-! The actual dominant ternary primary three in dimensions one through
three. Five coarse single-divisor scalar states retain integer floors;
the remaining dimension-two/six-point state uses the checked actual
shared cubic head. No improved top bound or group catalogue is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyTernaryLowerStep
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

theorem genRank_le_ceiling_of_dominant_three (hp : P.p = 2)
    (hd1 : 1 ≤ translationDimension J block P) (hd3 : translationDimension J block P ≤ 3)
    (i : block.Points)
    (hprimary : 3^(Fintype.card block.Points).factorization 3 = 3)
    (hother : ∀ r ∈ (Fintype.card block.Points).primeFactors, r ≠ 3 →
      r^(Fintype.card block.Points).factorization r ≤ 3)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let t := Fintype.card block.Points
  let d := translationDimension J block P
  let a := t.factorization 3
  let C : ℝ := totalMultiplicity d
  let m : ℝ := matchingMultiplicity d 3
  have ht : 2 ≤ t := by
    simpa only [t,Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have ht0 : t ≠ 0 := by omega
  have hd1' : 1 ≤ d := hd1
  have hd3' : d ≤ 3 := hd3
  have hd' : d = 1 ∨ d = 2 ∨ d = 3 := by omega
  have htCases := TinyComplementDominantTernaryDegree.degree_eq_three_or_six t ht0 hprimary hother
  by_cases hcritical : d = 2 ∧ t = 6
  · exact OriginalFourPointSharedSmallBinaryTopStep.genRank_le_ceiling_of_three_mul_binary
      J block P hp (show translationDimension J block P = 2 from hcritical.1) i 1
      (by decide) (by decide) (by simpa only [show (3 : ℕ)*2^1 = 6 by decide] using hcritical.2) htop
  have ha : a = 1 := Nat.pow_right_injective (by decide : 2 ≤ 3)
    (by simpa only [pow_one] using (show 3^a = 3 from hprimary))
  have hcost : (MarkedC4.genRank J : ℝ) ≤
      (t : ℝ)*(m/2+(C-m)/3)+MarkedC4.genRank block.Top := by
    have hh := genRank_le_single_divisor_rates J block P hp i 3 a Nat.prime_three
      (Nat.ordProj_dvd t 3)
    have hhr : (MarkedC4.genRank J : ℝ) ≤ m*(t : ℝ)*primaryRate 3 a+
        (C-m)*(t : ℝ)/(3 : ℝ)^a+MarkedC4.genRank block.Top := by
      simpa only [twoDivisorCost,Nat.cast_one,one_pow,one_div_one,
        min_eq_left (primaryRate_le_one 3 a)] using hh
    have hu : primaryRate 3 a = (1/2 : ℝ) := by norm_num [primaryRate,ha]
    rw [ha,pow_one] at hhr
    rw [show primaryRate 3 1 = (1/2 : ℝ) by simpa only [ha] using hu] at hhr
    convert hhr using 1 <;> ring
  have hCeq : C = (BinaryGeneralLinearSmallExactMultiplicities.smallTotal d : ℝ) := by
    dsimp only [C]
    rw [BinaryGeneralLinearSmallExactMultiplicities.totalMultiplicity_eq d (by omega)]
  have hmeq : m = (BinaryGeneralLinearSmallExactMultiplicities.smallOddMatching d 3 : ℝ) := by
    dsimp only [m]
    rw [BinaryGeneralLinearSmallExactMultiplicities.matching_odd_eq d 3 (by omega) (by decide)]
  have hcostNat : MarkedC4.genRank J ≤
      TinyTernaryLowerCeilingCertificates.headCut d t+MarkedC4.genRank block.Top := by
    rw [hCeq,hmeq] at hcost
    have hR : (MarkedC4.genRank J : ℝ) <
        ((TinyTernaryLowerCeilingCertificates.headCut d t+MarkedC4.genRank block.Top+1 : ℕ) : ℝ) := by
      rcases hd' with hdEq | hdEq | hdEq <;> rcases htCases with htEq | htEq
      all_goals try omega
      all_goals
        have hc := hcost
        norm_num [hdEq,htEq,BinaryGeneralLinearSmallExactMultiplicities.smallTotal,
          BinaryGeneralLinearSmallExactMultiplicities.smallOddMatching] at hc
        norm_num [hdEq,htEq,TinyTernaryLowerCeilingCertificates.headCut]
        linarith only [hc]
    have hN : MarkedC4.genRank J <
        TinyTernaryLowerCeilingCertificates.headCut d t+MarkedC4.genRank block.Top+1 := by
      exact_mod_cast hR
    omega
  have htopNat : MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling t := by
    simpa only [t,Fintype.card_eq_nat_card] using htop
  have hallowed : d ≠ 2 ∨ t ≠ 6 := by omega
  have hscalar := TinyTernaryLowerCeilingCertificates.aggregate_small d t (MarkedC4.genRank J)
    hd' htCases hallowed (hcostNat.trans (Nat.add_le_add_left htopNat _))
  have hn : n = 2^d*t := by
    calc
      n = Nat.card block.Fibre*Nat.card block.Points := by
        simpa only [Nat.card_fin] using block.degree_product.symm
      _ = 2^d*t := by
        rw [fibre_card_eq_prime_pow_dimension J block P,hp]
        simp only [d,t,Fintype.card_eq_nat_card]
  exact hscalar.trans_eq (congrArg traceyPermutationGeneratorCeiling hn).symm

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyTernaryLowerStep
