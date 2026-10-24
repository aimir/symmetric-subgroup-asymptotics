import SymmetricSubgroupAsymptotics.OriginalBinaryAffineExactChooseDivisorCost
import SymmetricSubgroupAsymptotics.ComplementaryLargeIntervalCeilingAggregation
import SymmetricSubgroupAsymptotics.BinaryGeneralLinearSmallOddMatching
import SymmetricSubgroupAsymptotics.LargestPrimePowerEntropy
import SymmetricSubgroupAsymptotics.TraceyElementarySeventeenQuarterEntropy

/-! The original arbitrary-top binary affine action is paid on the whole
large complementary-power interval. The dominant power and the second
power belong to the actual top factorization. The only generator input
is the genuine smaller-top coarse ceiling; no scalar-fit premise or
classification of the component or top is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineLargeComplementaryTail
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

theorem genRank_le_ceiling_of_large_other_power (hp : P.p = 2)
    (hd6 : translationDimension J block P ≤ 6) (i : block.Points) (q : ℕ)
    (hq : q ∈ (Fintype.card block.Points).primeFactors)
    (hsupport : q ∈ ({2,3,5,7,31} : Finset ℕ))
    (ha : (Fintype.card block.Points).factorization q < 128)
    (hM : 64 ≤ q^(Fintype.card block.Points).factorization q)
    (hmax : ∀ r ∈ (Fintype.card block.Points).primeFactors,
      r^(Fintype.card block.Points).factorization r ≤
        q^(Fintype.card block.Points).factorization q)
    (hother : ∃ r ∈ (Fintype.card block.Points).primeFactors, r ≠ q ∧
      16 ≤ r^(Fintype.card block.Points).factorization r)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let t := Fintype.card block.Points
  let d := translationDimension J block P
  let a := t.factorization q
  let M := q^a
  let C : ℝ := totalMultiplicity d
  let m : ℝ := matchingMultiplicity d q
  have ha127 : a ≤ 127 := Nat.le_of_lt_succ ha
  have ht : 2 ≤ t := by
    simpa only [t,Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have hprime := Nat.prime_of_mem_primeFactors hq
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
  have hmA : m ≤ ((d+d*(d-1)/2 : ℕ) : ℝ) := by
    dsimp only [m]
    exact_mod_cast matchingMultiplicity_le_triangle d q
  have htri : ((d+d*(d-1)/2 : ℕ) : ℝ) = (d : ℝ)*((d : ℝ)+1)/2 := by
    have hdiv := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self d)
    have hsub : d-1+1 = d := by omega
    have hmul := congrArg (fun x : ℕ => d*x) hsub
    have heq : 2*(d+d*(d-1)/2) = d*(d+1) := by nlinarith only [hdiv,hmul]
    have heqR : (2 : ℝ)*((d+d*(d-1)/2 : ℕ) : ℝ) = (d : ℝ)*((d : ℝ)+1) := by
      exact_mod_cast heq
    linarith only [heqR]
  have hmA' : m ≤ (d : ℝ)*((d : ℝ)+1)/2 := hmA.trans_eq htri
  have hlogM : Real.logb 2 (M : ℝ) = (a : ℝ)*Real.logb 2 (q : ℝ) := by
    simp only [M,Nat.cast_pow,Real.logb_pow]
  have hlog : Real.logb 2 (M : ℝ) ≤ 127 ∨
      (m ≤ (d : ℝ)-1 ∧ Real.logb 2 (M : ℝ) ≤ 635) := by
    by_cases hq2 : q = 2
    · left
      rw [hlogM,hq2]
      norm_num only [Nat.cast_ofNat]
      rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one]
      exact_mod_cast ha127
    · right
      have hpred := BinaryGeneralLinearSmallOddMatching.matchingMultiplicity_odd_le_pred
        d q hd6 hq2
      have hmPred : m ≤ (d : ℝ)-1 := by
        have hh : m ≤ ((d-1 : ℕ) : ℝ) := by dsimp only [m]; exact_mod_cast hpred
        simpa only [Nat.cast_sub hd1,Nat.cast_one] using hh
      refine ⟨hmPred,?_⟩
      have hq32 : q ≤ 32 := by
        simp only [Finset.mem_insert,Finset.mem_singleton] at hsupport
        omega
      have hlogq : Real.logb 2 (q : ℝ) ≤ 5 := by
        have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
          (by exact_mod_cast hprime.pos : (0 : ℝ) < q)
          (by exact_mod_cast hq32 : (q : ℝ) ≤ 32)
        have heq : Real.logb 2 (32 : ℝ) = 5 := by
          rw [show (32 : ℝ) = 2^5 by norm_num,Real.logb_pow,
            Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one]
          norm_num
        simpa only [heq] using hh
      have haR : (a : ℝ) ≤ 127 := by exact_mod_cast ha127
      have hh := mul_le_mul_of_nonneg_left hlogq (show (0 : ℝ) ≤ a by positivity)
      rw [hlogM]
      nlinarith only [hh,haR]
  obtain ⟨v,hv,hpowers,hchoice⟩ := TraceyElementaryLogBudget.exists_largest_other_power q t
  have hv16 : 16 ≤ v := by
    obtain ⟨r,hr,hrq,hr16⟩ := hother
    exact hr16.trans (hpowers r hr hrq)
  have hvM := LargestPrimePowerEntropy.largest_other_le t q v hprime hmax hchoice
  obtain ⟨r,hr,hrq,hvr⟩ := hchoice.resolve_left (by omega : v ≠ 1)
  have hrprime := Nat.prime_of_mem_primeFactors hr
  have hcost0 : (MarkedC4.genRank J : ℝ) ≤
      (t : ℝ)*(m*min (ActualWreathChooseDivisorCapacity.primaryRate q a) (1/(v : ℝ))+
        (C-m)/(M : ℝ)) + MarkedC4.genRank block.Top := by
    calc
      _ ≤ twoDivisorCost d t q a r (t.factorization r) + MarkedC4.genRank block.Top :=
        genRank_le_two_divisor_rates J block P hp i q a r (t.factorization r)
          hprime (Nat.ordProj_dvd t q) hrprime (Nat.ordProj_dvd t r) (Ne.symm hrq)
      _ = _ := by
        simp only [twoDivisorCost,hvr,Nat.cast_pow]
        dsimp only [m,C,M]
        push_cast
        ring
  have hmin : m*min (ActualWreathChooseDivisorCapacity.primaryRate q a) (1/(v : ℝ)) ≤
      m/(v : ℝ) := by
    simpa only [div_eq_mul_inv,one_mul] using
      mul_le_mul_of_nonneg_left
        (min_le_right (ActualWreathChooseDivisorCapacity.primaryRate q a) (1/(v : ℝ))) hm0
  have hcost : (MarkedC4.genRank J : ℝ) ≤
      (t : ℝ)*(m/(v : ℝ)+(C-m)/(M : ℝ)) + MarkedC4.genRank block.Top :=
    hcost0.trans (add_le_add (mul_le_mul_of_nonneg_left
      (add_le_add hmin le_rfl) (show (0 : ℝ) ≤ t by positivity)) le_rfl)
  have htopR : (MarkedC4.genRank block.Top : ℝ) ≤
      (traceyPermutationGeneratorCeiling t : ℝ) := by
    exact_mod_cast (show MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling t by
      simpa only [t,Fintype.card_eq_nat_card] using htop)
  change (MarkedC4.genRank block.Top : ℝ) ≤
    (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) at htopR
  have hcost' := hcost.trans (add_le_add le_rfl htopR)
  have hentropy : Real.logb 2 (t : ℝ) ≤ Real.logb 2 (M : ℝ)+(17/4)*(v : ℝ) := by
    rw [hlogM]
    exact TraceyElementarySeventeenQuarterEntropy.log_budget q t v hprime (by omega) hv hpowers
  have hreal := ComplementaryLargeIntervalCeilingAggregation.aggregate_le M d t hM hd1 hd6 ht
    (Nat.le_of_dvd (by omega : 0 < t) (Nat.ordProj_dvd t q)) C m (v : ℝ)
    (MarkedC4.genRank J : ℝ) hm0 hmC hC hmA' (by exact_mod_cast hv16)
    (by exact_mod_cast hvM) hlog hentropy hcost'
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

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineLargeComplementaryTail
