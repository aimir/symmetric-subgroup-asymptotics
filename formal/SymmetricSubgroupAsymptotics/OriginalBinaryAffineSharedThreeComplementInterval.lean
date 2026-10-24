import SymmetricSubgroupAsymptotics.OriginalFourPointSharedChooseCost
import SymmetricSubgroupAsymptotics.BinaryAffineSharedSmallComplementInterval
import SymmetricSubgroupAsymptotics.BinarySmallThreeComplementDegree
import SymmetricSubgroupAsymptotics.OriginalBinaryAffinePrimeMultiplicitySteps

/-! An original-action shared-head interval. The genuine smaller-top
coarse ceiling is retained. The literal complement-power guard is reduced
to a pure binary degree or three times the actual binary primary part;
the critical exponents six and seven are covered as one rational interval.
No fitted scalar inequality, current-degree Tracey bound, or action census
is an input. Other binary and small-primary frontiers remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineSharedThreeComplementInterval
open OriginalAffineBlockCharacteristicHead ActualWreathChooseDivisorCapacity

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem genRank_le_ceiling_of_three_mul_binary (hp : P.p = 2)
    (hdim : translationDimension J block P = 2) (i : block.Points)
    (a : ℕ) (ha6 : 6 ≤ a) (ha7 : a ≤ 7)
    (hshape : Fintype.card block.Points = 3 * 2 ^ a)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let t := Fintype.card block.Points
  let u := primaryRate 2 a
  have hfour : Nat.card block.Fibre = 4 := by
    calc
      Nat.card block.Fibre = P.p ^ translationDimension J block P :=
        fibre_card_eq_prime_pow_dimension J block P
      _ = 2 ^ translationDimension J block P :=
        congrArg (fun p : ℕ => p ^ translationDimension J block P) hp
      _ = 2 ^ (2 : ℕ) := congrArg (fun d : ℕ => 2 ^ d) hdim
      _ = 4 := by decide
  have hdiv : 2 ^ a ∣ t := by
    change 2 ^ a ∣ Fintype.card block.Points
    rw [hshape]
    exact ⟨3,by ring⟩
  have hh := OriginalFourPointSharedChooseCost.genRank_le_shared_primary_choose
    J block P hfour hp hdim i a hdiv
  have hcoef := BinaryAffineSharedSmallComplementInterval.shared_choose_coefficient_le a ha6
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hfirst : 2 * (t : ℝ) * u ≤ (53 / 64 : ℝ) * t := by
    calc
      2 * (t : ℝ) * u = (t : ℝ) * (2 * u) := by ring
      _ ≤ (t : ℝ) * (53 / 64 : ℝ) :=
        mul_le_mul_of_nonneg_left ((le_max_left _ _).trans hcoef) ht0
      _ = (53 / 64 : ℝ) * t := mul_comm _ _
  have hsecond : (t : ℝ) / 2 + (t : ℝ) * u + (t : ℝ) / (2 : ℝ) ^ a ≤
      (53 / 64 : ℝ) * t := by
    calc
      (t : ℝ) / 2 + (t : ℝ) * u + (t : ℝ) / (2 : ℝ) ^ a =
          (t : ℝ) * ((1 / 2 : ℝ) + u + 1 / (2 : ℝ) ^ a) := by ring
      _ ≤ (t : ℝ) * (53 / 64 : ℝ) :=
        mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hcoef) ht0
      _ = (53 / 64 : ℝ) * t := mul_comm _ _
  have htopR : (MarkedC4.genRank block.Top : ℝ) ≤
      (traceyPermutationGeneratorCeiling t : ℝ) := by
    exact_mod_cast (show MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling t by
      simpa only [t,Fintype.card_eq_nat_card] using htop)
  change (MarkedC4.genRank block.Top : ℝ) ≤
    (⌈(t : ℝ) / Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) at htopR
  have hcost : (MarkedC4.genRank J : ℝ) ≤ (53 / 64 : ℝ) * t +
      (⌈(t : ℝ) / Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) :=
    hh.trans (add_le_add (max_le hfirst hsecond) htopR)
  obtain ⟨ht192,hlower,hupper⟩ :=
    BinarySmallThreeComplementDegree.interval_of_three_mul_binary t a ha6 ha7 hshape
  have hreal := BinaryAffineSharedSmallComplementInterval.aggregate_le
    t ht192 hlower hupper (MarkedC4.genRank J : ℝ) hcost
  have hn : n = 4 * t := by
    calc
      n = Nat.card block.Fibre * Nat.card block.Points := by
        simpa only [Nat.card_fin] using block.degree_product.symm
      _ = 4 * t := by rw [hfour]; simp only [t,Fintype.card_eq_nat_card]
  have hnR : (n : ℝ) = 4 * (t : ℝ) := by exact_mod_cast hn
  have hlogfour : Real.logb 2 (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num,Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hlogn : Real.logb 2 (n : ℝ) = 2 + Real.logb 2 (t : ℝ) := by
    rw [hnR,Real.logb_mul (by norm_num : (4 : ℝ) ≠ 0) htpos.ne',hlogfour]
  have htarget : (MarkedC4.genRank J : ℝ) ≤ (n : ℝ) / Real.sqrt (Real.logb 2 (n : ℝ)) := by
    rw [hlogn,hnR]
    exact hreal
  have hfinal := htarget.trans (Nat.le_ceil ((n : ℝ) / Real.sqrt (Real.logb 2 (n : ℝ))))
  change (MarkedC4.genRank J : ℝ) ≤ (traceyPermutationGeneratorCeiling n : ℝ) at hfinal
  exact_mod_cast hfinal

theorem genRank_le_ceiling_of_other_powers_le_three (hp : P.p = 2)
    (hdim : translationDimension J block P = 2) (i : block.Points)
    (ha6 : 6 ≤ (Fintype.card block.Points).factorization 2)
    (ha7 : (Fintype.card block.Points).factorization 2 ≤ 7)
    (hother : ∀ q ∈ (Fintype.card block.Points).primeFactors, q ≠ 2 →
      q ^ (Fintype.card block.Points).factorization q ≤ 3)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  have ht : Fintype.card block.Points ≠ 0 := Fintype.card_ne_zero
  rcases BinarySmallThreeComplementDegree.eq_binary_or_three_mul
      (Fintype.card block.Points) ht hother with hbinary | hthree
  · exact OriginalBinaryAffinePrimeMultiplicitySteps.genRank_le_ceiling J block P hp
      ((Fintype.card block.Points).factorization 2) (by omega) hbinary i htop
  · exact genRank_le_ceiling_of_three_mul_binary J block P hp hdim i
      ((Fintype.card block.Points).factorization 2) ha6 ha7 hthree htop

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineSharedThreeComplementInterval
