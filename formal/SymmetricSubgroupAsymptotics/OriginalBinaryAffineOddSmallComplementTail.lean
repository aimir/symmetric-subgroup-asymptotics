import SymmetricSubgroupAsymptotics.OriginalBinaryAffineExactChooseDivisorCost
import SymmetricSubgroupAsymptotics.ExactChoosePrimaryRateBounds
import SymmetricSubgroupAsymptotics.OddSmallComplementCeilingAggregation
import SymmetricSubgroupAsymptotics.BinaryGeneralLinearSmallOddMatching

/-! Uniform original-action closure for an odd primary power at least
64 with all other actual prime powers below sixteen. No dominance,
exponent cutoff, prime list or fitted scalar estimate is assumed. The
translation head and actual complement chief costs use genuine divisor
weights; only the original smaller-top coarse ceiling is an input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineOddSmallComplementTail
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

theorem genRank_le_ceiling_of_odd_primary (hp : P.p = 2)
    (hd6 : translationDimension J block P ≤ 6) (i : block.Points) (q : ℕ)
    (hq : q ∈ (Fintype.card block.Points).primeFactors) (hq2 : q ≠ 2)
    (hM : 64 ≤ q^(Fintype.card block.Points).factorization q)
    (hsmall : ∀ r ∈ (Fintype.card block.Points).primeFactors, r ≠ q →
      r^(Fintype.card block.Points).factorization r < 16)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let t := Fintype.card block.Points
  let d := translationDimension J block P
  let a := t.factorization q
  let C : ℝ := totalMultiplicity d
  let m : ℝ := matchingMultiplicity d q
  have ht : 2 ≤ t := by
    simpa only [t,Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have hprime := Nat.prime_of_mem_primeFactors hq
  have hq3 : 3 ≤ q := by have hh := hprime.two_le; omega
  have ha1 : 1 ≤ a := by
    have hh : a ≠ 0 := Finsupp.mem_support_iff.mp hq
    omega
  have hd1 : 1 ≤ d := by
    by_contra hh
    have hz : d = 0 := by omega
    have hcard := fibre_card_eq_prime_pow_dimension J block P
    rw [hp,show translationDimension J block P = 0 from hz,pow_zero] at hcard
    have hf := block.degrees_ge_two.1
    omega
  have hm0 : 0 ≤ m := by positivity
  have hmCnat : matchingMultiplicity d q ≤ totalMultiplicity d := by
    have hval := pair_factorizations_le_cardFactors
      (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))) q (q+1) (by omega)
    unfold matchingMultiplicity totalMultiplicity
    split_ifs <;> omega
  have hmC : m ≤ C := by
    dsimp only [m,C]
    exact_mod_cast hmCnat
  have hC : C ≤ (d : ℝ)^2 := by
    dsimp only [C,totalMultiplicity]
    exact_mod_cast BinaryGeneralLinearTotalPrimeMultiplicity.dimension_add_GL_cardFactors_le_sq d
  have hmPred : m ≤ (d : ℝ)-1 := by
    have hh : m ≤ ((d-1 : ℕ) : ℝ) := by
      dsimp only [m]
      exact_mod_cast BinaryGeneralLinearSmallOddMatching.matchingMultiplicity_odd_le_pred d q hd6 hq2
    simpa only [Nat.cast_sub hd1,Nat.cast_one] using hh
  have hchoose : (MarkedC4.genRank J : ℝ) ≤
      (t : ℝ)*(m*ActualWreathChooseDivisorCapacity.primaryRate q a+
        (C-m)/(q : ℝ)^a) + MarkedC4.genRank block.Top := by
    calc
      _ ≤ twoDivisorCost d t q a 1 1 + MarkedC4.genRank block.Top :=
        genRank_le_single_divisor_rates J block P hp i q a hprime (Nat.ordProj_dvd t q)
      _ = _ := by
        simp only [twoDivisorCost,Nat.cast_one,one_pow,div_one,
          min_eq_left (primaryRate_le_one q a)]
        dsimp only [m,C]
        ring
  have hRate : ActualWreathChooseDivisorCapacity.primaryRate q a ≤
      BinaryAffineDominantPrimeSwitchNumerics.rate q a :=
    ExactChoosePrimaryRateBounds.primaryRate_le_sqrt q a hprime.two_le ha1
  have hcost : (MarkedC4.genRank J : ℝ) ≤
      (t : ℝ)*(m*BinaryAffineDominantPrimeSwitchNumerics.rate q a+
        (C-m)/(q : ℝ)^a) + MarkedC4.genRank block.Top :=
    hchoose.trans (add_le_add (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hRate hm0) le_rfl)
      (show (0 : ℝ) ≤ t by positivity)) le_rfl)
  have htopR : (MarkedC4.genRank block.Top : ℝ) ≤
      (traceyPermutationGeneratorCeiling t : ℝ) := by
    exact_mod_cast (show MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling t by
      simpa only [t,Fintype.card_eq_nat_card] using htop)
  change (MarkedC4.genRank block.Top : ℝ) ≤
    (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) at htopR
  have hcost' := hcost.trans (add_le_add le_rfl htopR)
  have hentropy := PrimeToSmallComplementEntropy.log_budget_of_other_powers_lt_sixteen
    q t hprime (by omega : t ≠ 0) hsmall
  have hreal := OddSmallComplementCeilingAggregation.aggregate_le q a d t hq3 ha1 hM
    hd1 hd6 ht (Nat.le_of_dvd (by omega : 0 < t) (Nat.ordProj_dvd t q))
    C m (MarkedC4.genRank J : ℝ) hm0 hmC hC hmPred hentropy hcost'
  have hn : n = 2^d*t := by
    calc
      n = Nat.card block.Fibre * Nat.card block.Points := by
        simpa only [Nat.card_fin] using block.degree_product.symm
      _ = 2^d*t := by
        rw [fibre_card_eq_prime_pow_dimension J block P,hp]
        simp only [d,t,Fintype.card_eq_nat_card]
  have hnR : (n : ℝ) = (2 : ℝ)^d*(t : ℝ) := by exact_mod_cast hn
  have hlogn : Real.logb 2 (n : ℝ) = (d : ℝ)+Real.logb 2 (t : ℝ) := by
    rw [hnR,Real.logb_mul (by positivity : (2 : ℝ)^d ≠ 0)
      (by exact_mod_cast (show t ≠ 0 by omega)),Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one]
  have htarget : (MarkedC4.genRank J : ℝ) ≤
      (n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ)) := by
    rw [hlogn,hnR]
    exact hreal
  have hfinal := htarget.trans (Nat.le_ceil ((n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ))))
  change (MarkedC4.genRank J : ℝ) ≤ (traceyPermutationGeneratorCeiling n : ℝ) at hfinal
  exact_mod_cast hfinal

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineOddSmallComplementTail
