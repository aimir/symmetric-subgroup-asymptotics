import SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyOddHigherStep
import SymmetricSubgroupAsymptotics.TinyComplementDominantTernaryDegree
import SymmetricSubgroupAsymptotics.TinyComplementHigherEnvelopes

/-! The actual dominant ternary primary of size three, on the original
binary affine block action. Complementary divisibility forces the top
degree to be three or six. The same literal chief-order coefficients and
the genuine smaller-top ceiling pay every dimension four through six. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyTernaryHigherStep
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
    (hd4 : 4 ≤ translationDimension J block P) (hd6 : translationDimension J block P ≤ 6)
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
  have hd4' : 4 ≤ d := hd4
  have hd6' : d ≤ 6 := hd6
  have ha : a = 1 := Nat.pow_right_injective (by decide : 2 ≤ 3)
    (by simpa only [pow_one] using (show 3^a = 3 from hprimary))
  have hmA : m ≤ (d : ℝ)-2 := by
    have hn := BinaryGeneralLinearOddSmallStrictMultiplicities.matching_odd_le_sub_two d 3
      hd4' hd6' (by decide)
    have hR : (matchingMultiplicity d 3 : ℝ) ≤ ((d-2 : ℕ) : ℝ) := by exact_mod_cast hn
    simpa only [m,Nat.cast_sub (by omega : 2 ≤ d),Nat.cast_ofNat] using hR
  have hC : C ≤ (d : ℝ)^2-2 := by
    have hn := BinaryGeneralLinearOddSmallStrictMultiplicities.total_le_square_sub_two d hd4' hd6'
    have hR : (totalMultiplicity d : ℝ) ≤ ((d^2-2 : ℕ) : ℝ) := by exact_mod_cast hn
    have hdSq : 2 ≤ d^2 := by nlinarith only [Nat.mul_le_mul hd4' hd4']
    simpa only [C,Nat.cast_sub hdSq,Nat.cast_pow,Nat.cast_ofNat] using hR
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
  have htopR : (MarkedC4.genRank block.Top : ℝ) ≤ (traceyPermutationGeneratorCeiling t : ℝ) := by
    exact_mod_cast (show MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling t by
      simpa only [t,Fintype.card_eq_nat_card] using htop)
  let L := Real.logb 2 (t : ℝ)
  have hL0 : 0 < L := Real.logb_pos (by norm_num) (by exact_mod_cast (show 1 < t by omega))
  have hscaled : (MarkedC4.genRank J : ℝ)*Real.sqrt ((d : ℝ)+L) ≤ (t : ℝ)*(2 : ℝ)^d := by
    rcases TinyComplementDominantTernaryDegree.degree_eq_three_or_six t ht0 hprimary hother with ht3 | ht6
    · have hc : traceyPermutationGeneratorCeiling 3 ≤ 3 :=
        IntegerLogSquareRootCeilingCertificate.ceil_le_of_square 3 1 1 3
          (by decide) (by decide) (by decide) (by decide) (by decide)
      have htop3 : (MarkedC4.genRank block.Top : ℝ) ≤ 3 := by
        have hh : (traceyPermutationGeneratorCeiling 3 : ℝ) ≤ 3 := by exact_mod_cast hc
        rw [ht3] at htopR
        exact htopR.trans hh
      have hg : (MarkedC4.genRank J : ℝ) ≤ (d : ℝ)^2+(d : ℝ)/2 := by
        rw [ht3] at hcost
        norm_num only [Nat.cast_ofNat] at hcost
        linarith only [hcost,htop3,hC,hmA]
      have hL : L ≤ 2 := by
        have hh := IntegerLogSquareRootCeilingCertificate.log_upper 3 1 2
          (by decide) (by decide) (by decide)
        simpa only [L,ht3,Nat.cast_one,div_one,Nat.cast_ofNat] using hh
      have hh := TinyComplementHigherEnvelopes.ternary_three_scaled_le d hd4'
        (MarkedC4.genRank J : ℝ) L hg hL
      simpa only [ht3,Nat.cast_ofNat] using hh
    · have hc : traceyPermutationGeneratorCeiling 6 ≤ 4 :=
        IntegerLogSquareRootCeilingCertificate.ceil_le_of_square 6 2 5 4
          (by decide) (by decide) (by decide) (by decide) (by decide)
      have htop6 : (MarkedC4.genRank block.Top : ℝ) ≤ 4 := by
        have hh : (traceyPermutationGeneratorCeiling 6 : ℝ) ≤ 4 := by exact_mod_cast hc
        rw [ht6] at htopR
        exact htopR.trans hh
      have hg : (MarkedC4.genRank J : ℝ) ≤ 2*(d : ℝ)^2+(d : ℝ)-2 := by
        rw [ht6] at hcost
        norm_num only [Nat.cast_ofNat] at hcost
        linarith only [hcost,htop6,hC,hmA]
      have hL : L ≤ 3 := by
        have hh := IntegerLogSquareRootCeilingCertificate.log_upper 6 1 3
          (by decide) (by decide) (by decide)
        simpa only [L,ht6,Nat.cast_one,div_one,Nat.cast_ofNat] using hh
      have hh := TinyComplementHigherEnvelopes.ternary_six_scaled_le d hd4'
        (MarkedC4.genRank J : ℝ) L hg hL
      simpa only [ht6,Nat.cast_ofNat] using hh
  have hs : 0 < Real.sqrt ((d : ℝ)+L) := Real.sqrt_pos.mpr (by positivity)
  have hreal : (MarkedC4.genRank J : ℝ) ≤
      (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+L) := by
    apply (le_div_iff₀ hs).mpr
    simpa only [mul_comm] using hscaled
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

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineTinyTernaryHigherStep
