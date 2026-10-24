import SymmetricSubgroupAsymptotics.OriginalBinaryAffineSingleDivisorCost
import SymmetricSubgroupAsymptotics.LargestPrimePowerEntropy
import SymmetricSubgroupAsymptotics.DominantPrimeCeilingAggregation

/-! A literal dominant-exponent tail for the ORIGINAL binary affine
block action in dimensions one through six. The dominant prime belongs
to the actual top-degree factorization. Only the genuine smaller-top
coarse ceiling is assumed. The empty complementary-prime case uses the
checked single-divisor bound; no prime chart is invented. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineDominantPrimeTail
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

theorem genRank_le_ceiling_of_dominant_exponent (hp : P.p = 2)
    (hd6 : translationDimension J block P ≤ 6) (i : block.Points) (q : ℕ)
    (hq : q ∈ (Fintype.card block.Points).primeFactors)
    (ha : 512 ≤ (Fintype.card block.Points).factorization q)
    (hmax : ∀ r ∈ (Fintype.card block.Points).primeFactors,
      r^(Fintype.card block.Points).factorization r ≤
        q^(Fintype.card block.Points).factorization q)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let t := Fintype.card block.Points
  let d := translationDimension J block P
  let a := t.factorization q
  let C : ℝ := totalMultiplicity d
  let m : ℝ := matchingMultiplicity d q
  have haLarge : 512 ≤ a := ha
  have ha1 : 1 ≤ a := by omega
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
  obtain ⟨v,hv,hpowers,hchoice⟩ := TraceyElementaryLogBudget.exists_largest_other_power q t
  have hvM := LargestPrimePowerEntropy.largest_other_le t q v hprime hmax hchoice
  have hcost : (MarkedC4.genRank J : ℝ) ≤
      (t : ℝ)*(m*min (BinaryAffineDominantPrimeSwitchNumerics.rate q a) (1/(v : ℝ))+
        (C-m)/(q : ℝ)^a) + MarkedC4.genRank block.Top := by
    rcases hchoice with rfl | ⟨r,hr,hrq,rfl⟩
    · calc
        _ ≤ twoDivisorCost d t q a 1 1 + MarkedC4.genRank block.Top :=
          OriginalBinaryAffineSingleDivisorCost.genRank_le_single_divisor_rates
            J block P hp i q a hprime ha1 (Nat.ordProj_dvd t q)
        _ = _ := by
          simp only [twoDivisorCost,Nat.cast_one,one_pow,div_one]
          dsimp only [m,C,primaryRate,BinaryAffineDominantPrimeSwitchNumerics.rate]
          ring
    · have hrprime := Nat.prime_of_mem_primeFactors hr
      have hf : 1 ≤ t.factorization r := by
        have hh : t.factorization r ≠ 0 := Finsupp.mem_support_iff.mp hr
        omega
      calc
        _ ≤ twoDivisorCost d t q a r (t.factorization r) + MarkedC4.genRank block.Top :=
          genRank_le_two_divisor_rates J block P hp i q a r (t.factorization r)
            hprime ha1 (Nat.ordProj_dvd t q) hrprime hf
            (Nat.ordProj_dvd t r) (Ne.symm hrq)
        _ = _ := by
          simp only [twoDivisorCost,Nat.cast_pow]
          dsimp only [m,C,primaryRate,BinaryAffineDominantPrimeSwitchNumerics.rate]
          ring
  have htopR : (MarkedC4.genRank block.Top : ℝ) ≤
      (traceyPermutationGeneratorCeiling t : ℝ) := by
    exact_mod_cast (show MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling t by
      simpa only [t,Fintype.card_eq_nat_card] using htop)
  change (MarkedC4.genRank block.Top : ℝ) ≤
    (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) at htopR
  have hcost' := hcost.trans (add_le_add le_rfl htopR)
  have hreal := DominantPrimeCeilingAggregation.aggregate_le q a d t hprime haLarge hd1 hd6 ht
    (Nat.le_of_dvd (by omega : 0 < t) (Nat.ordProj_dvd t q)) C m (v : ℝ)
    (MarkedC4.genRank J : ℝ) hm0 hmC hC hmA
    (by exact_mod_cast (show 0 < v by omega)) (by exact_mod_cast hvM)
    (TraceyElementarySharperLogBudget.log_budget_linear q t v hprime (by omega) hv hpowers) hcost'
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
    (ha : 512 ≤ (Fintype.card block.Points).factorization q)
    (hmax : ∀ r ∈ (Fintype.card block.Points).primeFactors,
      r^(Fintype.card block.Points).factorization r ≤
        q^(Fintype.card block.Points).factorization q)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧
      S.card ≤ traceyPermutationGeneratorCeiling n := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨S,hgen,hS.le.trans (genRank_le_ceiling_of_dominant_exponent
    J block P hp hd6 i q hq ha hmax htop)⟩

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineDominantPrimeTail
