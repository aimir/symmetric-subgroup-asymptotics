import SymmetricSubgroupAsymptotics.OriginalBinaryAffineExactChooseDivisorCost
import SymmetricSubgroupAsymptotics.ThreeComplementCeilingAggregation
import SymmetricSubgroupAsymptotics.OriginalBinaryAffineSharedThreeComplementInterval

/-! Every original binary affine action whose top degree has no other
primary power above three, once its binary primary part is at least64.
The two small dimension-two exponents use the checked actual shared-head
proof. All other cases use uniform scalar ranges; no census or fitted
inequality is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineThreeComplementInterval
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

theorem genRank_le_ceiling_of_three_mul_binary (hp : P.p = 2) (i : block.Points)
    (a : ℕ) (ha6 : 6 ≤ a) (hshape : Fintype.card block.Points = 3*2^a)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  by_cases hcritical : translationDimension J block P = 2 ∧ a ≤ 7
  · exact OriginalBinaryAffineSharedThreeComplementInterval.genRank_le_ceiling_of_three_mul_binary
      J block P hp hcritical.1 i a ha6 hcritical.2 hshape htop
  let t := Fintype.card block.Points
  let d := translationDimension J block P
  let C : ℝ := totalMultiplicity d
  let m : ℝ := matchingMultiplicity d 2
  have ht : 2 ≤ t := by
    simpa only [t,Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have ht0 : t ≠ 0 := by omega
  have hd1 : 1 ≤ d := by
    by_contra hh
    have hz : d = 0 := by omega
    have hcard := fibre_card_eq_prime_pow_dimension J block P
    rw [hp,show translationDimension J block P = 0 from hz,pow_zero] at hcard
    have hf := block.degrees_ge_two.1
    omega
  have hregime : 3 ≤ d ∨ 8 ≤ a ∨ d = 1 := by
    change ¬ (d = 2 ∧ a ≤ 7) at hcritical
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
  have hdiv2 : 2^a ∣ t := by
    rw [show t = 3*2^a from hshape]
    exact ⟨3,by ring⟩
  have hdiv3 : 3^1 ∣ t := by
    rw [show t = 3*2^a from hshape]
    exact ⟨2^a,by simp⟩
  have hcost0 : (MarkedC4.genRank J : ℝ) ≤
      (t : ℝ)*(m*min (ActualWreathChooseDivisorCapacity.primaryRate 2 a) (1/3)+
        (C-m)/(2 : ℝ)^a)+MarkedC4.genRank block.Top := by
    have hh := genRank_le_two_divisor_rates J block P hp i 2 a 3 1
      Nat.prime_two hdiv2 (by decide) hdiv3 (by decide)
    calc
      _ ≤ twoDivisorCost d t 2 a 3 1+MarkedC4.genRank block.Top := hh
      _ = _ := by
        dsimp only [twoDivisorCost,C,m]
        norm_num only [pow_one,Nat.cast_ofNat]
        ring
  have hmin := mul_le_mul_of_nonneg_left
    (min_le_left (ActualWreathChooseDivisorCapacity.primaryRate 2 a) (1/3 : ℝ)) hm0
  have hcost : (MarkedC4.genRank J : ℝ) ≤
      (t : ℝ)*(m*ActualWreathChooseDivisorCapacity.primaryRate 2 a+
        (C-m)/(2 : ℝ)^a)+MarkedC4.genRank block.Top :=
    hcost0.trans (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hmin le_rfl)
      (show (0 : ℝ) ≤ t by positivity)) le_rfl)
  have htopR : (MarkedC4.genRank block.Top : ℝ) ≤
      (traceyPermutationGeneratorCeiling t : ℝ) := by
    exact_mod_cast (show MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling t by
      simpa only [t,Fintype.card_eq_nat_card] using htop)
  change (MarkedC4.genRank block.Top : ℝ) ≤
    (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) at htopR
  have hreal := ThreeComplementCeilingAggregation.aggregate_le a d t ha6 hd1 hregime
    hshape C m (MarkedC4.genRank J : ℝ) hm0 hmC hC hmA
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

theorem genRank_le_ceiling_of_other_powers_le_three (hp : P.p = 2) (i : block.Points)
    (ha6 : 6 ≤ (Fintype.card block.Points).factorization 2)
    (hother : ∀ q ∈ (Fintype.card block.Points).primeFactors, q ≠ 2 →
      q^(Fintype.card block.Points).factorization q ≤ 3)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  have ht : Fintype.card block.Points ≠ 0 := Fintype.card_ne_zero
  rcases BinarySmallThreeComplementDegree.eq_binary_or_three_mul
      (Fintype.card block.Points) ht hother with hbinary | hthree
  · exact OriginalBinaryAffinePrimeMultiplicitySteps.genRank_le_ceiling J block P hp
      ((Fintype.card block.Points).factorization 2) (by omega) hbinary i htop
  · exact genRank_le_ceiling_of_three_mul_binary J block P hp i
      ((Fintype.card block.Points).factorization 2) ha6 hthree htop

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineThreeComplementInterval
