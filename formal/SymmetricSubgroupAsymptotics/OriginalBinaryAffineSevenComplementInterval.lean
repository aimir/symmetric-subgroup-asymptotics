import SymmetricSubgroupAsymptotics.OriginalBinaryAffineExactChooseDivisorCost
import SymmetricSubgroupAsymptotics.SevenComplementCeilingAggregation
import SymmetricSubgroupAsymptotics.BinarySmallComplementSevenEntropy
import SymmetricSubgroupAsymptotics.LargestPrimePowerEntropy

/-! The literal original affine block action on the whole complementary
power interval [7,15]. The binary primary exponent is arbitrary above
five. Both divisors, the complementary entropy, and the smaller-top
ceiling belong to the same actual top degree. No action catalogue or
scalar fitting premise is used. Small dominant powers remain separate. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineSevenComplementInterval
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

theorem genRank_le_ceiling_of_other_power_interval (hp : P.p = 2)
    (hd6 : translationDimension J block P ≤ 6) (i : block.Points)
    (ha6 : 6 ≤ (Fintype.card block.Points).factorization 2) (r : ℕ)
    (hr : r ∈ (Fintype.card block.Points).primeFactors) (hr2 : r ≠ 2)
    (hv7 : 7 ≤ r^(Fintype.card block.Points).factorization r)
    (hv15 : r^(Fintype.card block.Points).factorization r ≤ 15)
    (hother : ∀ q ∈ (Fintype.card block.Points).primeFactors, q ≠ 2 →
      q^(Fintype.card block.Points).factorization q ≤ r^(Fintype.card block.Points).factorization r)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let t := Fintype.card block.Points
  let d := translationDimension J block P
  let a := t.factorization 2
  let v := r^t.factorization r
  let B := Real.logb 2 (t / 2^a : ℕ)
  let C : ℝ := totalMultiplicity d
  let m : ℝ := matchingMultiplicity d 2
  have ht : 2 ≤ t := by
    simpa only [t,Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have ht0 : t ≠ 0 := by omega
  have hrprime := Nat.prime_of_mem_primeFactors hr
  have hproduct : 2^a*v ∣ t :=
    (Nat.coprime_pow_primes a (t.factorization r) Nat.prime_two hrprime
      (Ne.symm hr2)).mul_dvd_of_dvd_of_dvd (Nat.ordProj_dvd t 2) (Nat.ordProj_dvd t r)
  have hMv : 2^a*v ≤ t := Nat.le_of_dvd (by omega : 0 < t) hproduct
  have hpow64 : (64 : ℕ) ≤ 2^a := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) ha6
  have hv7' : 7 ≤ v := hv7
  have ht256 : 256 ≤ t := by nlinarith only [hMv,hpow64,hv7']
  have hL8 : 8 ≤ Real.logb 2 (t : ℝ) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 256) (by exact_mod_cast ht256 : (256 : ℝ) ≤ t)
    have heq : Real.logb 2 (256 : ℝ) = 8 := by
      rw [show (256 : ℝ) = 2^8 by norm_num,Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one]
      norm_num
    simpa only [heq] using hh
  obtain ⟨hB0,hB16,hBv⟩ :=
    BinarySmallComplementSevenEntropy.otherPart_log_bounds t v ht0 hv7 hv15 hother
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
      (t : ℝ)*(m*min (ActualWreathChooseDivisorCapacity.primaryRate 2 a) (1/(v : ℝ))+
        (C-m)/(2 : ℝ)^a)+MarkedC4.genRank block.Top := by
    have hh := genRank_le_two_divisor_rates J block P hp i 2 a r (t.factorization r)
      Nat.prime_two (Nat.ordProj_dvd t 2) hrprime (Nat.ordProj_dvd t r) (Ne.symm hr2)
    calc
      _ ≤ twoDivisorCost d t 2 a r (t.factorization r)+MarkedC4.genRank block.Top := hh
      _ = _ := by
        dsimp only [twoDivisorCost,v,C,m]
        push_cast
        ring
  have htopR : (MarkedC4.genRank block.Top : ℝ) ≤
      (traceyPermutationGeneratorCeiling t : ℝ) := by
    exact_mod_cast (show MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling t by
      simpa only [t,Fintype.card_eq_nat_card] using htop)
  change (MarkedC4.genRank block.Top : ℝ) ≤
    (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) at htopR
  have hreal := SevenComplementCeilingAggregation.aggregate_le a d t v ha6 hd1 hd6
    ht hv7 hMv C m B (MarkedC4.genRank J : ℝ) hm0 hmC hC hmA hB0 hB16 hBv
      hL8 hentropy (hcost.trans (add_le_add le_rfl htopR))
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

theorem genRank_le_ceiling_of_some_other_power_seven (hp : P.p = 2)
    (hd6 : translationDimension J block P ≤ 6) (i : block.Points)
    (ha6 : 6 ≤ (Fintype.card block.Points).factorization 2)
    (hother : ∀ q ∈ (Fintype.card block.Points).primeFactors, q ≠ 2 →
      q^(Fintype.card block.Points).factorization q < 16)
    (hexists : ∃ q ∈ (Fintype.card block.Points).primeFactors, q ≠ 2 ∧
      7 ≤ q^(Fintype.card block.Points).factorization q)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let t := Fintype.card block.Points
  obtain ⟨v,hv,hpowers,hchoice⟩ := TraceyElementaryLogBudget.exists_largest_other_power 2 t
  have hv7 : 7 ≤ v := by
    obtain ⟨q,hq,hq2,hq7⟩ := hexists
    exact hq7.trans (hpowers q hq hq2)
  obtain ⟨r,hr,hr2,hvr⟩ := hchoice.resolve_left (by omega : v ≠ 1)
  have hv15 : v ≤ 15 := by
    rw [hvr]
    exact Nat.le_of_lt_succ (show r^t.factorization r < 16 from hother r hr hr2)
  exact genRank_le_ceiling_of_other_power_interval J block P hp hd6 i ha6 r hr hr2
    (by simpa only [hvr] using hv7) (by simpa only [hvr] using hv15)
    (by simpa only [hvr] using hpowers) htop

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineSevenComplementInterval
