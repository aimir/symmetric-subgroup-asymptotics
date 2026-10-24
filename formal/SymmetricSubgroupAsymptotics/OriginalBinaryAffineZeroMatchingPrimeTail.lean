import SymmetricSubgroupAsymptotics.OriginalBinaryAffineSingleDivisorCost
import SymmetricSubgroupAsymptotics.LargestPrimePowerEntropy
import SymmetricSubgroupAsymptotics.ZeroMatchingPrimeCeilingAggregation

/-! The ORIGINAL binary affine block step when the actual dominant
prime power is at least64 and its SAME-GL matching coefficient vanishes.
The coefficient-zero condition is literal arithmetic, not a group-model
exclusion assumption. Actual smaller-top coarse rank is the only
permutation-generator premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineZeroMatchingPrimeTail
open OriginalAffineBlockCharacteristicHead OriginalBinaryAffineDominantDivisorCost
open BinaryGeneralLinearMatchingPrimeMultiplicity

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem genRank_le_ceiling_of_zero_matching (hp : P.p = 2)
    (hd6 : translationDimension J block P ≤ 6) (i : block.Points) (q : ℕ)
    (hq : q ∈ (Fintype.card block.Points).primeFactors)
    (hmax : ∀ r ∈ (Fintype.card block.Points).primeFactors,
      r^(Fintype.card block.Points).factorization r ≤
        q^(Fintype.card block.Points).factorization q)
    (hM : 64 ≤ q^(Fintype.card block.Points).factorization q)
    (hzero : matchingMultiplicity (translationDimension J block P) q = 0)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let t := Fintype.card block.Points
  let d := translationDimension J block P
  let a := t.factorization q
  let M := q^a
  let C : ℝ := totalMultiplicity d
  have ht : 2 ≤ t := by
    simpa only [t,Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have hprime := Nat.prime_of_mem_primeFactors hq
  have ha1 : 1 ≤ a := by
    have hh : t.factorization q ≠ 0 := Finsupp.mem_support_iff.mp hq
    change a ≠ 0 at hh
    omega
  have hd1 : 1 ≤ d := by
    by_contra hh
    have hz : d = 0 := by omega
    have hcard := fibre_card_eq_prime_pow_dimension J block P
    rw [hp,show translationDimension J block P = 0 from hz,pow_zero] at hcard
    have hf := block.degrees_ge_two.1
    omega
  have hC0 : 0 ≤ C := by positivity
  have hC : C ≤ (d : ℝ)^2 := by
    dsimp only [C,totalMultiplicity]
    exact_mod_cast BinaryGeneralLinearTotalPrimeMultiplicity.dimension_add_GL_cardFactors_le_sq d
  have hzero' : matchingMultiplicity d q = 0 := hzero
  have hcost : (MarkedC4.genRank J : ℝ) ≤
      (t : ℝ)*C/(M : ℝ)+MarkedC4.genRank block.Top := by
    calc
      _ ≤ twoDivisorCost d t q a 1 1+MarkedC4.genRank block.Top :=
        OriginalBinaryAffineSingleDivisorCost.genRank_le_single_divisor_rates
          J block P hp i q a hprime ha1 (Nat.ordProj_dvd t q)
      _ = _ := by
        simp only [twoDivisorCost,hzero',Nat.cast_zero,zero_mul,zero_add,sub_zero]
        dsimp only [C,M]
        rw [Nat.cast_pow]
        ring
  obtain ⟨v,hv,hpowers,hchoice⟩ := TraceyElementaryLogBudget.exists_largest_other_power q t
  have hvM := LargestPrimePowerEntropy.largest_other_le t q v hprime hmax hchoice
  have hMt : M ≤ t := Nat.le_of_dvd (by omega : 0 < t) (Nat.ordProj_dvd t q)
  have hlogM : Real.logb 2 (M : ℝ) = (a : ℝ)*Real.logb 2 (q : ℝ) := by
    simp only [M,Nat.cast_pow,Real.logb_pow]
  have hentropy : Real.logb 2 (t : ℝ) ≤ Real.logb 2 (M : ℝ)+8*(v : ℝ) := by
    rw [hlogM]
    exact TraceyElementarySharperLogBudget.log_budget_linear q t v hprime (by omega) hv hpowers
  have htopR : (MarkedC4.genRank block.Top : ℝ) ≤
      (traceyPermutationGeneratorCeiling t : ℝ) := by
    exact_mod_cast (show MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling t by
      simpa only [t,Fintype.card_eq_nat_card] using htop)
  change (MarkedC4.genRank block.Top : ℝ) ≤
    (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) at htopR
  have hcost' := hcost.trans (add_le_add le_rfl htopR)
  have hreal := ZeroMatchingPrimeCeilingAggregation.aggregate_le d t M hd1 hd6 hM hMt C
    (v : ℝ) (MarkedC4.genRank J : ℝ) hC0 hC (by positivity) (by exact_mod_cast hvM)
    hentropy hcost'
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

theorem exists_generating_finset (hp : P.p = 2)
    (hd6 : translationDimension J block P ≤ 6) (i : block.Points) (q : ℕ)
    (hq : q ∈ (Fintype.card block.Points).primeFactors)
    (hmax : ∀ r ∈ (Fintype.card block.Points).primeFactors,
      r^(Fintype.card block.Points).factorization r ≤
        q^(Fintype.card block.Points).factorization q)
    (hM : 64 ≤ q^(Fintype.card block.Points).factorization q)
    (hzero : matchingMultiplicity (translationDimension J block P) q = 0)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧
      S.card ≤ traceyPermutationGeneratorCeiling n := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨S,hgen,hS.le.trans (genRank_le_ceiling_of_zero_matching
    J block P hp hd6 i q hq hmax hM hzero htop)⟩

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineZeroMatchingPrimeTail
