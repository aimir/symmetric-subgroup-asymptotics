import SymmetricSubgroupAsymptotics.OriginalBinaryAffineExactChooseDivisorCost
import SymmetricSubgroupAsymptotics.FiveComplementCeilingAggregation
import SymmetricSubgroupAsymptotics.BinarySmallFiveComplementDegree
import SymmetricSubgroupAsymptotics.LargestPrimePowerEntropy

/-! The literal original affine action with complementary power five.
All affine dimensions and binary exponents above five are covered by a
single envelope. Both divisors, prime-to-binary entropy and the top ceiling
belong to the actual original action. No scalar-fit conclusion is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineFiveComplementInterval
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

theorem genRank_le_ceiling_of_other_power_five (hp : P.p = 2)
    (i : block.Points)
    (ha6 : 6 ≤ (Fintype.card block.Points).factorization 2) (r : ℕ)
    (hr : r ∈ (Fintype.card block.Points).primeFactors) (hr2 : r ≠ 2)
    (hv5 : r^(Fintype.card block.Points).factorization r = 5)
    (hother : ∀ q ∈ (Fintype.card block.Points).primeFactors, q ≠ 2 →
      q^(Fintype.card block.Points).factorization q ≤ 5)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let t := Fintype.card block.Points
  let d := translationDimension J block P
  let a := t.factorization 2
  let B := Real.logb 2 (t / 2^a : ℕ)
  let C : ℝ := totalMultiplicity d
  let m : ℝ := matchingMultiplicity d 2
  have ht : 2 ≤ t := by
    simpa only [t,Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have ht0 : t ≠ 0 := by omega
  have hrprime := Nat.prime_of_mem_primeFactors hr
  have hproduct0 : 2^a*(r^t.factorization r) ∣ t :=
    (Nat.coprime_pow_primes a (t.factorization r) Nat.prime_two hrprime
      (Ne.symm hr2)).mul_dvd_of_dvd_of_dvd (Nat.ordProj_dvd t 2) (Nat.ordProj_dvd t r)
  have hv5' : r^t.factorization r = 5 := hv5
  have hproduct : 2^a*5 ∣ t := by simpa only [hv5'] using hproduct0
  have hMt : 2^a*5 ≤ t := Nat.le_of_dvd (by omega : 0 < t) hproduct
  have hL : 33/4 ≤ Real.logb 2 (t : ℝ) := by
    have hh := BinarySmallFiveComplementDegree.degree_log_lower t a hMt
    have haR : (6 : ℝ) ≤ a := by exact_mod_cast ha6
    linarith only [hh,haR]
  obtain ⟨hB0,hB4⟩ := BinarySmallFiveComplementDegree.otherPart_log_bounds t ht0 hother
  have hprod : (t : ℝ) = (2 : ℝ)^a*((t / 2^a : ℕ) : ℝ) := by
    exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self t 2).symm
  have hentropy : Real.logb 2 (t : ℝ) ≤ (a : ℝ)+B := by
    have hotherpos : (0 : ℝ) < (t / 2^a : ℕ) := by
      exact_mod_cast Nat.ordCompl_pos 2 ht0
    rw [hprod,Real.logb_mul (by positivity : (2 : ℝ)^a ≠ 0) hotherpos.ne',
      Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one]
  have hd1 : 1 ≤ d := by
    by_contra hh
    have hz : d = 0 := by omega
    have hcard := fibre_card_eq_prime_pow_dimension J block P
    rw [hp,show translationDimension J block P = 0 from hz,pow_zero] at hcard
    have hf := block.degrees_ge_two.1
    omega
  have hm0 : 0 ≤ m := by positivity
  have hmC : m ≤ C := by
    have hh := pair_factorizations_le_cardFactors
      (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))) 2 3 (by decide)
    have hn : matchingMultiplicity d 2 ≤ totalMultiplicity d := by
      unfold matchingMultiplicity totalMultiplicity
      simp only [if_true]
      omega
    dsimp only [m,C]
    exact_mod_cast hn
  have hC : C ≤ (d : ℝ)^2 := by
    dsimp only [C,totalMultiplicity]
    exact_mod_cast BinaryGeneralLinearTotalPrimeMultiplicity.dimension_add_GL_cardFactors_le_sq d
  have hmA : m ≤ (d : ℝ)*((d : ℝ)+1)/2 := by
    have hh := matchingMultiplicity_le_triangle d 2
    have heven := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self d)
    have hsub : d-1+1 = d := by omega
    have hmul := congrArg (fun x : ℕ => d*x) hsub
    have heq : 2*(d+d*(d-1)/2) = d*(d+1) := by nlinarith only [heven,hmul]
    have heqR : (2 : ℝ)*((d+d*(d-1)/2 : ℕ) : ℝ) = (d : ℝ)*((d : ℝ)+1) := by
      exact_mod_cast heq
    have hhR : m ≤ ((d+d*(d-1)/2 : ℕ) : ℝ) := by
      dsimp only [m]
      exact_mod_cast hh
    linarith only [hhR,heqR]
  have hcost : (MarkedC4.genRank J : ℝ) ≤
      (t : ℝ)*(m*min (ActualWreathChooseDivisorCapacity.primaryRate 2 a) (1/5)+
        (C-m)/(2 : ℝ)^a)+MarkedC4.genRank block.Top := by
    have hh := genRank_le_two_divisor_rates J block P hp i 2 a r (t.factorization r)
      Nat.prime_two (Nat.ordProj_dvd t 2) hrprime (Nat.ordProj_dvd t r) (Ne.symm hr2)
    calc
      _ ≤ twoDivisorCost d t 2 a r (t.factorization r)+MarkedC4.genRank block.Top := hh
      _ = _ := by
        dsimp only [twoDivisorCost,C,m]
        push_cast
        rw [show (r : ℝ)^t.factorization r = 5 by exact_mod_cast hv5']
        ring
  have htopR : (MarkedC4.genRank block.Top : ℝ) ≤
      (traceyPermutationGeneratorCeiling t : ℝ) := by
    exact_mod_cast (show MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling t by
      simpa only [t,Fintype.card_eq_nat_card] using htop)
  change (MarkedC4.genRank block.Top : ℝ) ≤
    (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) at htopR
  have hreal := FiveComplementCeilingAggregation.aggregate_le a d t ha6 hd1 ht
    hMt C m B (MarkedC4.genRank J : ℝ) hm0 hmC hC hmA hB0 hB4 hL hentropy
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

theorem genRank_le_ceiling_of_other_powers_le_five (hp : P.p = 2) (i : block.Points)
    (ha6 : 6 ≤ (Fintype.card block.Points).factorization 2)
    (hother : ∀ q ∈ (Fintype.card block.Points).primeFactors, q ≠ 2 →
      q^(Fintype.card block.Points).factorization q ≤ 5)
    (hexists : ∃ q ∈ (Fintype.card block.Points).primeFactors, q ≠ 2 ∧
      5 ≤ q^(Fintype.card block.Points).factorization q)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let t := Fintype.card block.Points
  obtain ⟨v,hv,hpowers,hchoice⟩ := TraceyElementaryLogBudget.exists_largest_other_power 2 t
  have hv5 : 5 ≤ v := by
    obtain ⟨q,hq,hq2,hq5⟩ := hexists
    exact hq5.trans (hpowers q hq hq2)
  obtain ⟨r,hr,hr2,hvr⟩ := hchoice.resolve_left (by omega : v ≠ 1)
  have hfive : r^t.factorization r = 5 := by
    apply Nat.le_antisymm (show r^t.factorization r ≤ 5 from hother r hr hr2)
    exact hvr ▸ hv5
  exact genRank_le_ceiling_of_other_power_five J block P hp i ha6 r hr hr2 hfive hother htop

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineFiveComplementInterval
