import SymmetricSubgroupAsymptotics.OriginalBinaryAffineSmallZeroMatchingStep
import SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementAllCeiling

/-! An actual all-dimension small-primary complementary interval. Every
coefficient is the literal SAME GL order, every divisor belongs to the
original block top, and the only inductive input is its genuine coarse
ceiling. The residual export keeps actual complementary powers<=4
explicit; no full Tracey theorem or action catalogue is claimed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineSmallPrimaryComplementStep
open OriginalAffineBlockCharacteristicHead OriginalBinaryAffineExactChooseDivisorCost
open OriginalBinaryAffineDominantDivisorCost (totalMultiplicity)
open BinaryGeneralLinearMatchingPrimeMultiplicity

private theorem degree_log_le (q t v : ℕ) (hq : q.Prime) (ht : t ≠ 0)
    (hv : 1 ≤ v) (hv63 : v ≤ 63)
    (hpower : ∀ r ∈ t.primeFactors, r ≠ q → r^t.factorization r ≤ v) :
    Real.logb 2 (t : ℝ) ≤ Real.logb 2 ((q : ℝ)^t.factorization q)+(3/2)*(v : ℝ) := by
  have hdeg := TraceyElementarySharperLogBudget.degree_le_primary_mul_lcm q t v ht hv hpower
  have hdegR : (t : ℝ) ≤ (q : ℝ)^t.factorization q*(Nat.lcmUpto v : ℝ) := by
    exact_mod_cast hdeg
  have ht0 : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero ht
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hlcm0 : (0 : ℝ) < Nat.lcmUpto v := by exact_mod_cast Nat.lcmUpto_pos v
  calc
    Real.logb 2 (t : ℝ) ≤ Real.logb 2
        ((q : ℝ)^t.factorization q*(Nat.lcmUpto v : ℝ)) :=
      Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) ht0 hdegR
    _ = Real.logb 2 ((q : ℝ)^t.factorization q)+Real.logb 2 (Nat.lcmUpto v : ℝ) := by
      rw [Real.logb_mul (pow_ne_zero _ hq0.ne') hlcm0.ne']
    _ ≤ Real.logb 2 ((q : ℝ)^t.factorization q)+(3/2)*(v : ℝ) :=
      add_le_add le_rfl (SmallPrimaryLcmEntropy.log_lcm_le v hv63)

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem genRank_le_ceiling_of_large_complement (hp : P.p = 2)
    (i : block.Points) (q r : ℕ)
    (hq : q ∈ (Fintype.card block.Points).primeFactors)
    (hr : r ∈ (Fintype.card block.Points).primeFactors) (hrq : r ≠ q)
    (hmax : ∀ s ∈ (Fintype.card block.Points).primeFactors,
      s^(Fintype.card block.Points).factorization s ≤ q^(Fintype.card block.Points).factorization q)
    (hM : q^(Fintype.card block.Points).factorization q < 64)
    (hv : 5 ≤ r^(Fintype.card block.Points).factorization r)
    (hother : ∀ s ∈ (Fintype.card block.Points).primeFactors, s ≠ q →
      s^(Fintype.card block.Points).factorization s ≤ r^(Fintype.card block.Points).factorization r)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let t := Fintype.card block.Points
  let d := translationDimension J block P
  let a := t.factorization q
  let b := t.factorization r
  let M := q^a
  let v := r^b
  let C : ℝ := totalMultiplicity d
  let m : ℝ := matchingMultiplicity d q
  have ht : 2 ≤ t := by
    simpa only [t,Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have ht0 : t ≠ 0 := by omega
  have hqprime := Nat.prime_of_mem_primeFactors hq
  have hrprime := Nat.prime_of_mem_primeFactors hr
  have hM64 : M < 64 := hM
  have hv5 : 5 ≤ v := hv
  have hvM : v ≤ M := hmax r hr
  have hv63 : v ≤ 63 := by omega
  have hvR : (5 : ℝ) ≤ v := by exact_mod_cast hv
  have hv0 : (0 : ℝ) < v := by linarith only [hvR]
  have hMR : (v : ℝ) ≤ M := by exact_mod_cast hvM
  have hM0 : (0 : ℝ) < M := hv0.trans_le hMR
  have hdiv : M*v ∣ t :=
    (Nat.coprime_pow_primes a b hqprime hrprime hrq.symm).mul_dvd_of_dvd_of_dvd
      (Nat.ordProj_dvd t q) (Nat.ordProj_dvd t r)
  have hproduct : q^a*v ≤ t := Nat.le_of_dvd (by omega : 0 < t) hdiv
  have hcop : Nat.Coprime (q^a) v := Nat.coprime_pow_primes a b hqprime hrprime hrq.symm
  have hd1 : 1 ≤ d := by
    by_contra hh
    have hz : d = 0 := by omega
    have hcard := fibre_card_eq_prime_pow_dimension J block P
    rw [hp,show translationDimension J block P = 0 from hz,pow_zero] at hcard
    have hf := block.degrees_ge_two.1
    omega
  have hm0 : 0 ≤ m := by positivity
  have hcost : (MarkedC4.genRank J : ℝ) ≤
      (t : ℝ)*SmallPrimaryLargeComplementAllCeiling.rate d q a (v : ℝ)+
        MarkedC4.genRank block.Top := by
    have hh := genRank_le_two_divisor_rates J block P hp i q a r b hqprime
      (Nat.ordProj_dvd t q) hrprime (Nat.ordProj_dvd t r) hrq.symm
    have hfirst := mul_le_mul_of_nonneg_left
      (min_le_right (ActualWreathChooseDivisorCapacity.primaryRate q a) (1/(v : ℝ)))
      (mul_nonneg hm0 (show (0 : ℝ) ≤ t by positivity))
    have hbound : twoDivisorCost d t q a r b ≤
        (t : ℝ)*SmallPrimaryLargeComplementAllCeiling.rate d q a (v : ℝ) := by
      change m*(t : ℝ)*min (ActualWreathChooseDivisorCapacity.primaryRate q a)
          (1/(r : ℝ)^b)+(C-m)*(t : ℝ)/(q : ℝ)^a ≤ _
      have hrpow : (r : ℝ)^b = (v : ℝ) := by simp only [v,Nat.cast_pow]
      rw [hrpow]
      change _ ≤ (t : ℝ)*(m/(v : ℝ)+(C-m)/(q : ℝ)^a)
      calc
        _ ≤ m*(t : ℝ)*(1/(v : ℝ))+(C-m)*(t : ℝ)/(q : ℝ)^a :=
          add_le_add hfirst le_rfl
        _ = _ := by ring
    exact hh.trans (add_le_add hbound le_rfl)
  have hentropy := degree_log_le q t v hqprime ht0 (by omega) hv63 hother
  have htopR : (MarkedC4.genRank block.Top : ℝ) ≤
      (traceyPermutationGeneratorCeiling t : ℝ) := by
    exact_mod_cast (show MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling t by
      simpa only [t,Fintype.card_eq_nat_card] using htop)
  change (MarkedC4.genRank block.Top : ℝ) ≤
    (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) at htopR
  have hreal := SmallPrimaryLargeComplementAllCeiling.aggregate_le q a v d t hqprime hd1
    hv hvM hM64 hcop hproduct hentropy (MarkedC4.genRank J : ℝ)
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


theorem genRank_le_ceiling_or_small_complement (hp : P.p = 2) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n ∨
      ∃ q ∈ (Fintype.card block.Points).primeFactors,
        q ∈ ({2,3,5,7,31} : Finset ℕ) ∧
        (∀ r ∈ (Fintype.card block.Points).primeFactors,
          r^(Fintype.card block.Points).factorization r ≤
            q^(Fintype.card block.Points).factorization q) ∧
        q^(Fintype.card block.Points).factorization q < 64 ∧
        ∀ r ∈ (Fintype.card block.Points).primeFactors, r ≠ q →
          r^(Fintype.card block.Points).factorization r ≤ 4 := by
  classical
  obtain hbound | ⟨q,hq,hsupport,hmax,hsmall⟩ :=
    OriginalBinaryAffineSmallZeroMatchingStep.genRank_le_ceiling_or_supported_small_primary
      J block P hp i htop
  · exact Or.inl hbound
  · by_cases hfour : ∀ r ∈ (Fintype.card block.Points).primeFactors, r ≠ q →
        r^(Fintype.card block.Points).factorization r ≤ 4
    · exact Or.inr ⟨q,hq,hsupport,hmax,hsmall,hfour⟩
    · obtain ⟨v,hv,hpower,hchoice⟩ := TraceyElementaryLogBudget.exists_largest_other_power
        q (Fintype.card block.Points)
      have hv5 : 5 ≤ v := by
        by_contra hh
        have hv4 : v ≤ 4 := by omega
        exact hfour (fun r hr hrq => (hpower r hr hrq).trans hv4)
      rcases hchoice with hv1 | ⟨r,hr,hrq,hvshape⟩
      · omega
      · exact Or.inl (genRank_le_ceiling_of_large_complement J block P hp i q r hq hr hrq
          hmax hsmall (by simpa only [← hvshape] using hv5)
          (by simpa only [← hvshape] using hpower) htop)

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineSmallPrimaryComplementStep
