import SymmetricSubgroupAsymptotics.OriginalBinaryAffineDominantDivisorCost

/-! The complementary-prime EMPTY case of the actual dominant-divisor
cost. The value one is only a scalar bound for an empty complementary
factorization; no prime chart with parameter one is invented. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineSingleDivisorCost
open OriginalAffineBlockCharacteristicHead OriginalBinaryAffineWeightedOrderCost
open ActualWreathChiefWeightedPrimeBudget ActualWreathChiefDivisorWeights
open ActualDivisorWeightRateBounds PrimeMultiplicityTwoRateBound
open BinaryGeneralLinearMatchingPrimeMultiplicity OriginalBinaryAffineDominantDivisorCost

theorem primaryRate_le_one (q a : ℕ) (hq : q.Prime) (ha : 1 ≤ a) :
    primaryRate q a ≤ 1 := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hprod := mul_le_mul (by linarith : (1 : ℝ) ≤ (q : ℝ)-1) haR
    (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (0 : ℝ) ≤ (q : ℝ)-1)
  have hden : 0 < 3*((q : ℝ)-1)*a :=
    mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
  apply Real.sqrt_le_iff.mpr
  refine ⟨by norm_num,?_⟩
  apply (div_le_iff₀ hden).mpr
  nlinarith only [hprod]

private theorem head_weighted_le (d M q : ℕ) (weight : ℕ → ℝ)
    (primary other : ℝ) (hprimary : weight q ≤ primary)
    (hother : ∀ p, p ≠ q → weight p ≤ other) :
    (d : ℝ)*weight 2 + weightedOrder weight M ≤
      ((M.factorization q : ℝ)+(if q = 2 then (d : ℝ) else 0))*primary +
      ((d : ℝ)+(ArithmeticFunction.cardFactors M : ℝ)-
        ((M.factorization q : ℝ)+(if q = 2 then (d : ℝ) else 0)))*other := by
  have hw := weightedOrder_le_two_rates weight M q primary other hprimary hother
  by_cases hq : q = 2
  · subst q
    have hh := add_le_add
      (mul_le_mul_of_nonneg_left hprimary (show (0 : ℝ) ≤ d by positivity)) hw
    simp only [if_true]
    nlinarith only [hh]
  · have hh := add_le_add
      (mul_le_mul_of_nonneg_left (hother 2 (Ne.symm hq))
        (show (0 : ℝ) ≤ d by positivity)) hw
    simp only [if_neg hq]
    nlinarith only [hh]

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem genRank_le_single_divisor_rates (hp : P.p = 2) (i : block.Points)
    (q a : ℕ) (hq : q.Prime) (ha : 1 ≤ a) (hqd : q^a ∣ Fintype.card block.Points) :
    (MarkedC4.genRank J : ℝ) ≤
      twoDivisorCost (translationDimension J block P)
        (Fintype.card block.Points) q a 1 1 + MarkedC4.genRank block.Top := by
  let t := Fintype.card block.Points
  let d := translationDimension J block P
  let M := Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))
  let weight := divisorWeight t q a
  have ht : 2 ≤ t := by
    simpa only [t,Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have hprimary : weight q ≤ (t : ℝ)*primaryRate q a := by
    simpa only [weight,divisorRate,if_pos rfl,primaryRate] using
      divisorWeight_le_divisorRate t q a q ht hq ha hqd
  have hother (p : ℕ) (hpq : p ≠ q) : weight p ≤ (t : ℝ)/(q : ℝ)^a := by
    simpa only [weight,divisorRate,if_neg hpq] using
      divisorWeight_le_divisorRate t q a p ht hq ha hqd
  have hcost := head_weighted_le d M q weight ((t : ℝ)*primaryRate q a)
    ((t : ℝ)/(q : ℝ)^a) hprimary hother
  have hrank := genRank_le_divisorWeight J block P hp i q a hq ha hqd
  have hcombined := hrank.trans (add_le_add hcost le_rfl)
  simpa only [twoDivisorCost,totalMultiplicity,matchingMultiplicity,
    Nat.cast_add,Nat.cast_ite,Nat.cast_zero,Nat.cast_one,one_pow,div_one,
    min_eq_left (primaryRate_le_one q a hq ha),mul_assoc,mul_div_assoc,d,M,t,weight] using hcombined

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineSingleDivisorCost
