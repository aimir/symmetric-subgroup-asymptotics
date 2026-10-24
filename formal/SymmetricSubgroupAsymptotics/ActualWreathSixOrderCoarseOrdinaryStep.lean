import SymmetricSubgroupAsymptotics.ActualWreathSixOrderJointLogCost
import SymmetricSubgroupAsymptotics.ActualWreathSixOrderDivisorCost
import SymmetricSubgroupAsymptotics.OrderSixJointCoarseCeilingNumerics
import SymmetricSubgroupAsymptotics.SmallMatchingDominantPrimaryDegrees
import SymmetricSubgroupAsymptotics.OrderSixTinyCoarseCeilingCertificates

/-! An independent coarse ordinary-generator recurrence for actual
correlated wreath states whose local order divides6. Every prime regime
and all top degrees are paid. Only the genuine top coarse ceiling is
assumed; no global Tracey/MN bound or fitted numerical field occurs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathSixOrderCoarseOrdinaryStep
open ActualWreathOrdinaryChiefRecurrence OrderSixTinyCoarseCeilingCertificates

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]

private theorem tiny_cost {S : ActualWreathCompressionState Q I} {i : I} {c : ℕ}
    (hc : ChiefCost i S c) (hI : 2 ≤ Fintype.card I) (horder : Nat.card S.D ∣ 6)
    (ht : Fintype.card I = 2 ∨ Fintype.card I = 3 ∨ Fintype.card I = 4 ∨
      Fintype.card I = 6 ∨ Fintype.card I = 12) : c ≤ bodyCut (Fintype.card I) := by
  rcases ht with hdeg | hdeg | hdeg | hdeg | hdeg
  · have hd : 2^1 ∣ Fintype.card I := by rw [hdeg]; decide
    have hh := ActualWreathSixOrderDivisorCost.cost_le_divisor_rates hc hI horder
      2 1 (by decide) hd
    rw [hdeg] at hh
    norm_num [ActualWreathChooseDivisorCapacity.divisorRate,
      ActualWreathChooseDivisorCapacity.primaryRate] at hh
    have hcn : c ≤ 2 := by exact_mod_cast hh
    simpa only [hdeg,bodyCut,ite_true,ite_false,show (2 : ℕ) ≠ 3 by decide,
      show (3 : ℕ) ≠ 2 by decide,show (4 : ℕ) ≠ 2 by decide,
      show (4 : ℕ) ≠ 3 by decide,show (6 : ℕ) ≠ 2 by decide,
      show (6 : ℕ) ≠ 3 by decide,show (6 : ℕ) ≠ 4 by decide,
      show (12 : ℕ) ≠ 2 by decide,show (12 : ℕ) ≠ 3 by decide,
      show (12 : ℕ) ≠ 4 by decide,show (12 : ℕ) ≠ 6 by decide] using hcn
  · have hd : 3^1 ∣ Fintype.card I := by rw [hdeg]; decide
    have hh := ActualWreathSixOrderDivisorCost.cost_le_divisor_rates hc hI horder
      3 1 (by decide) hd
    rw [hdeg] at hh
    norm_num [ActualWreathChooseDivisorCapacity.divisorRate,
      ActualWreathChooseDivisorCapacity.primaryRate] at hh
    have hcR : (c : ℝ) < 3 := by linarith only [hh]
    have hcN : c < 3 := by exact_mod_cast hcR
    have hcn : c ≤ 2 := by omega
    simpa only [hdeg,bodyCut,ite_true,ite_false,show (2 : ℕ) ≠ 3 by decide,
      show (3 : ℕ) ≠ 2 by decide,show (4 : ℕ) ≠ 2 by decide,
      show (4 : ℕ) ≠ 3 by decide,show (6 : ℕ) ≠ 2 by decide,
      show (6 : ℕ) ≠ 3 by decide,show (6 : ℕ) ≠ 4 by decide,
      show (12 : ℕ) ≠ 2 by decide,show (12 : ℕ) ≠ 3 by decide,
      show (12 : ℕ) ≠ 4 by decide,show (12 : ℕ) ≠ 6 by decide] using hcn
  · have hd : 2^2 ∣ Fintype.card I := by rw [hdeg]; decide
    have hh := ActualWreathSixOrderDivisorCost.cost_le_divisor_rates hc hI horder
      2 2 (by decide) hd
    rw [hdeg] at hh
    norm_num [ActualWreathChooseDivisorCapacity.divisorRate,
      ActualWreathChooseDivisorCapacity.primaryRate] at hh
    have hcn : c ≤ 3 := by exact_mod_cast hh
    simpa only [hdeg,bodyCut,ite_true,ite_false,show (2 : ℕ) ≠ 3 by decide,
      show (3 : ℕ) ≠ 2 by decide,show (4 : ℕ) ≠ 2 by decide,
      show (4 : ℕ) ≠ 3 by decide,show (6 : ℕ) ≠ 2 by decide,
      show (6 : ℕ) ≠ 3 by decide,show (6 : ℕ) ≠ 4 by decide,
      show (12 : ℕ) ≠ 2 by decide,show (12 : ℕ) ≠ 3 by decide,
      show (12 : ℕ) ≠ 4 by decide,show (12 : ℕ) ≠ 6 by decide] using hcn
  · have hd : 3^1 ∣ Fintype.card I := by rw [hdeg]; decide
    have hh := ActualWreathSixOrderDivisorCost.cost_le_divisor_rates hc hI horder
      3 1 (by decide) hd
    rw [hdeg] at hh
    norm_num [ActualWreathChooseDivisorCapacity.divisorRate,
      ActualWreathChooseDivisorCapacity.primaryRate] at hh
    have hcn : c ≤ 5 := by exact_mod_cast hh
    simpa only [hdeg,bodyCut,ite_true,ite_false,show (2 : ℕ) ≠ 3 by decide,
      show (3 : ℕ) ≠ 2 by decide,show (4 : ℕ) ≠ 2 by decide,
      show (4 : ℕ) ≠ 3 by decide,show (6 : ℕ) ≠ 2 by decide,
      show (6 : ℕ) ≠ 3 by decide,show (6 : ℕ) ≠ 4 by decide,
      show (12 : ℕ) ≠ 2 by decide,show (12 : ℕ) ≠ 3 by decide,
      show (12 : ℕ) ≠ 4 by decide,show (12 : ℕ) ≠ 6 by decide] using hcn
  · have hd : 2^2 ∣ Fintype.card I := by rw [hdeg]; decide
    have hh := ActualWreathSixOrderDivisorCost.cost_le_divisor_rates hc hI horder
      2 2 (by decide) hd
    rw [hdeg] at hh
    norm_num [ActualWreathChooseDivisorCapacity.divisorRate,
      ActualWreathChooseDivisorCapacity.primaryRate] at hh
    have hcn : c ≤ 9 := by exact_mod_cast hh
    simpa only [hdeg,bodyCut,ite_true,ite_false,show (2 : ℕ) ≠ 3 by decide,
      show (3 : ℕ) ≠ 2 by decide,show (4 : ℕ) ≠ 2 by decide,
      show (4 : ℕ) ≠ 3 by decide,show (6 : ℕ) ≠ 2 by decide,
      show (6 : ℕ) ≠ 3 by decide,show (6 : ℕ) ≠ 4 by decide,
      show (12 : ℕ) ≠ 2 by decide,show (12 : ℕ) ≠ 3 by decide,
      show (12 : ℕ) ≠ 4 by decide,show (12 : ℕ) ≠ 6 by decide] using hcn

private theorem rank_ceiling_of_real (S : ActualWreathCompressionState Q I)
    (hI : 2 ≤ Fintype.card I)
    (hreal : (MarkedC4.genRank S.A : ℝ) ≤ 3*(Fintype.card I : ℝ)/
      Real.sqrt (Real.logb 2 (3 : ℝ)+Real.logb 2 (Fintype.card I : ℝ))) :
    MarkedC4.genRank S.A ≤ traceyPermutationGeneratorCeiling (3*Fintype.card I) := by
  have hlog : Real.logb 2 ((3*Fintype.card I : ℕ) : ℝ) =
      Real.logb 2 (3 : ℝ)+Real.logb 2 (Fintype.card I : ℝ) := by
    rw [Nat.cast_mul,Nat.cast_ofNat,Real.logb_mul (by norm_num : (3 : ℝ) ≠ 0)
      (by exact_mod_cast (show Fintype.card I ≠ 0 by omega))]
  have hh : (MarkedC4.genRank S.A : ℝ) ≤ ((3*Fintype.card I : ℕ) : ℝ)/
      Real.sqrt (Real.logb 2 ((3*Fintype.card I : ℕ) : ℝ)) := by
    rw [hlog,Nat.cast_mul,Nat.cast_ofNat]
    exact hreal
  have hf := hh.trans (Nat.le_ceil (((3*Fintype.card I : ℕ) : ℝ)/
    Real.sqrt (Real.logb 2 ((3*Fintype.card I : ℕ) : ℝ))))
  change (MarkedC4.genRank S.A : ℝ) ≤
    (traceyPermutationGeneratorCeiling (3*Fintype.card I) : ℝ) at hf
  exact_mod_cast hf

theorem genRank_le_ceiling (S : ActualWreathCompressionState Q I) (i : I)
    (hI : 2 ≤ Fintype.card I) (horder : Nat.card S.D ∣ 6)
    (htop : MarkedC4.genRank Q ≤ traceyPermutationGeneratorCeiling (Fintype.card I)) :
    MarkedC4.genRank S.A ≤ traceyPermutationGeneratorCeiling (3*Fintype.card I) := by
  let t := Fintype.card I
  obtain ⟨q,hq,hmax⟩ := LargestPrimePowerEntropy.exists_largest_prime_power t hI
  have hqprime := Nat.prime_of_mem_primeFactors hq
  let a := t.factorization q
  let M := q^a
  have hdiv : q^a ∣ Fintype.card I := Nat.ordProj_dvd t q
  have hMt : M ≤ t := Nat.le_of_dvd (by omega : 0 < t) hdiv
  have hMpos : (0 : ℝ) < M := by
    exact_mod_cast (show 0 < M from pow_pos hqprime.pos a)
  obtain ⟨c,hc,hgen,hcostLog,hcostHalf⟩ := ActualWreathSixOrderJointLogCost.exists_cost
    S i hI horder q a hqprime hdiv hmax
  have htopR : (MarkedC4.genRank Q : ℝ) ≤
      (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) := by exact_mod_cast htop
  have hgenR : (MarkedC4.genRank S.A : ℝ) ≤ (c : ℝ)+MarkedC4.genRank Q := by
    exact_mod_cast hgen
  have hs0 : 0 ≤ Real.logb 2 (3 : ℝ) := Real.logb_nonneg (by norm_num) (by norm_num)
  have hs : Real.logb 2 (3 : ℝ) ≤ 8/5 := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_upper 3 5 8
      (by decide) (by decide) (by decide)
    simpa only [Nat.cast_ofNat] using hh
  by_cases hM8 : 8 ≤ M
  · apply rank_ceiling_of_real S hI
    apply OrderSixJointCoarseCeilingNumerics.large_primary_aggregate t (by omega)
      (Real.logb 2 (3 : ℝ)) (MarkedC4.genRank S.A : ℝ) hs0 hs
    · exact hgenR.trans (add_le_add (hcostHalf hM8) htopR)
    · exact hgenR.trans (add_le_add hcostLog htopR)
  · have hM7 : M ≤ 7 := by omega
    by_cases hq23 : q = 2 ∨ q = 3
    · have hsmall : q^t.factorization q < 8 := by
        simpa only [M,a] using (show M < 8 by omega)
      have htiny := SmallMatchingDominantPrimaryDegrees.degree_eq t q hI hq hmax hsmall hq23
      have hbody := tiny_cost hc hI horder htiny
      have htopCut : MarkedC4.genRank Q ≤ topCut t :=
        htop.trans (top_ceiling_le t htiny)
      exact hgen.trans ((Nat.add_le_add hbody htopCut).trans (cuts_le_target_ceiling t htiny))
    · have hq2 : q ≠ 2 := by omega
      have hq3 : q ≠ 3 := by omega
      have hq5 : 5 ≤ q := by
        have hodd := hqprime.odd_of_ne_two hq2
        have hm := Nat.odd_iff.mp hodd
        have hh := hqprime.two_le
        omega
      have ha : 1 ≤ a := by
        have hh : t.factorization q ≠ 0 := Finsupp.mem_support_iff.mp hq
        dsimp only [a]
        omega
      have hqM : q ≤ M := by
        simpa only [pow_one] using Nat.pow_le_pow_right hqprime.pos ha
      have hM5 : 5 ≤ M := hq5.trans hqM
      have hlocal := ActualWreathSixOrderDivisorCost.cost_le_two_primeTo hc hI horder
        q a hqprime hdiv hq2 hq3
      have hlocal' : (c : ℝ) ≤ 2*(t : ℝ)/(M : ℝ) := by
        simpa only [t,M,Nat.cast_pow] using hlocal
      have hcost : (c : ℝ) ≤ (2/5)*(t : ℝ) := by
        apply hlocal'.trans
        apply (div_le_iff₀ hMpos).mpr
        have hM5R : (5 : ℝ) ≤ M := by exact_mod_cast hM5
        have hh := mul_le_mul_of_nonneg_left hM5R (show (0 : ℝ) ≤ t by positivity)
        nlinarith only [hh]
      have hd := LargestPrimePowerQuadraticEntropy.degree_dvd_lcmUpto t 7 (by omega)
        (by decide) (fun p hp => (hmax p hp).trans hM7)
      have ht420 : t ≤ 420 := by
        have hh := Nat.le_of_dvd (Nat.lcmUpto_pos 7) hd
        simpa only [show Nat.lcmUpto 7 = 420 by decide] using hh
      have hL9 : Real.logb 2 (t : ℝ) ≤ 9 := by
        have hh := IntegerLogSquareRootCeilingCertificate.log_upper t 1 9 (by omega)
          (by decide) (by simpa only [pow_one] using (show t ≤ 2^9 by omega))
        simpa only [Nat.cast_ofNat,Nat.cast_one,div_one] using hh
      apply rank_ceiling_of_real S hI
      exact OrderSixJointCoarseCeilingNumerics.small_nonmatching_aggregate t (by omega)
        (Real.logb 2 (3 : ℝ)) (MarkedC4.genRank S.A : ℝ) hs0 hs hL9
        (hgenR.trans (add_le_add hcost htopR))

theorem exists_generating_finset (S : ActualWreathCompressionState Q I) (i : I)
    (hI : 2 ≤ Fintype.card I) (horder : Nat.card S.D ∣ 6)
    (htop : MarkedC4.genRank Q ≤ traceyPermutationGeneratorCeiling (Fintype.card I)) :
    ∃ F : Finset S.A, Subgroup.closure (F : Set S.A) = ⊤ ∧
      F.card ≤ traceyPermutationGeneratorCeiling (3*Fintype.card I) := by
  obtain ⟨F,hF,hgen⟩ := MarkedC4.genRank_spec (G := S.A)
  exact ⟨F,hgen,hF.le.trans (genRank_le_ceiling S i hI horder htop)⟩

end SymmetricSubgroupAsymptotics.ActualWreathSixOrderCoarseOrdinaryStep
