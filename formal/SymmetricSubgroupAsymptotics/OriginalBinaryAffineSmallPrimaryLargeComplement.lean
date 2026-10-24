import SymmetricSubgroupAsymptotics.OriginalBinaryAffineSmallZeroMatchingStep
import SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementCeiling

/-! An actual supported-small-primary interval. The dominant and
complementary powers are literal divisors of the original block top;
normal chief coordinates and the same local GL order remain unchanged.
The only inductive input is the genuine smaller-top coarse ceiling.
This export covers dimension>=4 and complementary primary>=5; it makes
no claim about the remaining small-dimensional or small-complement states. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineSmallPrimaryLargeComplement
open OriginalAffineBlockCharacteristicHead OriginalBinaryAffineExactChooseDivisorCost
open OriginalBinaryAffineDominantDivisorCost (totalMultiplicity)
open BinaryGeneralLinearMatchingPrimeMultiplicity

private theorem degree_log_le (q t v : ℕ) (hq : q.Prime) (ht : t ≠ 0)
    (hv : 1 ≤ v) (hv63 : v ≤ 63) (hM : q^t.factorization q ≤ 64)
    (hpower : ∀ r ∈ t.primeFactors, r ≠ q → r^t.factorization r ≤ v) :
    Real.logb 2 (t : ℝ) ≤ 6+(3/2)*(v : ℝ) := by
  have hdeg := TraceyElementarySharperLogBudget.degree_le_primary_mul_lcm q t v ht hv hpower
  have hdegR : (t : ℝ) ≤ (q : ℝ)^t.factorization q*(Nat.lcmUpto v : ℝ) := by
    exact_mod_cast hdeg
  have ht0 : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero ht
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hlcm0 : (0 : ℝ) < Nat.lcmUpto v := by exact_mod_cast Nat.lcmUpto_pos v
  have hMlog : Real.logb 2 ((q : ℝ)^t.factorization q) ≤ 6 := by
    have hMR : (q : ℝ)^t.factorization q ≤ (2 : ℝ)^6 := by exact_mod_cast hM
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (pow_pos hq0 _) hMR
    have hlog64 : Real.logb 2 ((2 : ℝ)^6) = 6 := by
      rw [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one]
      norm_num
    simpa only [hlog64] using hh
  calc
    Real.logb 2 (t : ℝ) ≤ Real.logb 2
        ((q : ℝ)^t.factorization q*(Nat.lcmUpto v : ℝ)) :=
      Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) ht0 hdegR
    _ = Real.logb 2 ((q : ℝ)^t.factorization q)+Real.logb 2 (Nat.lcmUpto v : ℝ) := by
      rw [Real.logb_mul (pow_ne_zero _ hq0.ne') hlcm0.ne']
    _ ≤ 6+(3/2)*(v : ℝ) := add_le_add hMlog (SmallPrimaryLcmEntropy.log_lcm_le v hv63)

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem genRank_le_ceiling_of_large_complement (hp : P.p = 2)
    (hd : 4 ≤ translationDimension J block P) (i : block.Points) (q r : ℕ)
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
  have hproduct : v^2 ≤ t := by
    have hh := Nat.le_of_dvd (by omega : 0 < t) hdiv
    have hmul := Nat.mul_le_mul_right v hvM
    nlinarith only [hh,hmul]
  have hm0 : 0 ≤ m := by positivity
  have hmC : m ≤ C := by
    have hh := pair_factorizations_le_cardFactors
      (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))) q (q+1) (by omega)
    have hn : matchingMultiplicity d q ≤ totalMultiplicity d := by
      unfold matchingMultiplicity totalMultiplicity
      split_ifs <;> omega
    dsimp only [m,C]
    exact_mod_cast hn
  have hC0 : 0 ≤ C := by positivity
  have hC : C ≤ (d : ℝ)^2 := by
    dsimp only [C,totalMultiplicity]
    exact_mod_cast BinaryGeneralLinearTotalPrimeMultiplicity.dimension_add_GL_cardFactors_le_sq d
  have hcost : (MarkedC4.genRank J : ℝ) ≤
      (t : ℝ)*C/(v : ℝ)+MarkedC4.genRank block.Top := by
    have hh := genRank_le_two_divisor_rates J block P hp i q a r b hqprime
      (Nat.ordProj_dvd t q) hrprime (Nat.ordProj_dvd t r) hrq.symm
    have hrate : 1/(M : ℝ) ≤ 1/(v : ℝ) := one_div_le_one_div_of_le hv0 hMR
    have hfirst := mul_le_mul_of_nonneg_left
      (min_le_right (ActualWreathChooseDivisorCapacity.primaryRate q a) (1/(v : ℝ)))
      (mul_nonneg hm0 (show (0 : ℝ) ≤ t by positivity))
    have hsecond := mul_le_mul_of_nonneg_left hrate
      (mul_nonneg (sub_nonneg.mpr hmC) (show (0 : ℝ) ≤ t by positivity))
    have hbound : twoDivisorCost d t q a r b ≤ (t : ℝ)*C/(v : ℝ) := by
      change m*(t : ℝ)*min (ActualWreathChooseDivisorCapacity.primaryRate q a)
          (1/(r : ℝ)^b)+(C-m)*(t : ℝ)/(q : ℝ)^a ≤ _
      have hqpow : (q : ℝ)^a = (M : ℝ) := by simp only [M,Nat.cast_pow]
      have hrpow : (r : ℝ)^b = (v : ℝ) := by simp only [v,Nat.cast_pow]
      rw [hqpow,hrpow]
      have hs := add_le_add hfirst hsecond
      convert hs using 1 <;> ring
    exact hh.trans (add_le_add hbound le_rfl)
  have hentropy := degree_log_le q t v hqprime ht0 (by omega) hv63
    (show q^t.factorization q ≤ 64 from Nat.le_of_lt hM64) hother
  have htopR : (MarkedC4.genRank block.Top : ℝ) ≤
      (traceyPermutationGeneratorCeiling t : ℝ) := by
    exact_mod_cast (show MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling t by
      simpa only [t,Fintype.card_eq_nat_card] using htop)
  change (MarkedC4.genRank block.Top : ℝ) ≤
    (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) at htopR
  have hreal := SmallPrimaryLargeComplementCeiling.aggregate_le v d t hv hd hproduct C
    (MarkedC4.genRank J : ℝ) hC0 hC hentropy (hcost.trans (add_le_add le_rfl htopR))
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

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineSmallPrimaryLargeComplement
