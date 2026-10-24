import SymmetricSubgroupAsymptotics.OriginalBinaryAffineChooseWeightedCost
import SymmetricSubgroupAsymptotics.OriginalBinaryAffineDominantDivisorCost
import Mathlib.Data.Nat.Choose.Bounds

/-! Exact choose-on-divisor ordinary costs on the ORIGINAL block action.
Both displayed primary powers divide the actual top degree. The matching
coefficient and all remaining prime multiplicities belong to the SAME
literal binary GL order. The complementary-empty export uses the scalar
one only, never a fictitious prime or coordinate chart of order one. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineExactChooseDivisorCost
open OriginalAffineBlockCharacteristicHead OriginalBinaryAffineChooseWeightedCost
open ActualWreathChooseDivisorCapacity ActualWreathChiefWeightedPrimeBudget
open PrimeMultiplicityTwoRateBound BinaryGeneralLinearMatchingPrimeMultiplicity
open OriginalBinaryAffineDominantDivisorCost (totalMultiplicity)

def twoDivisorCost (d t q e r f : ℕ) : ℝ :=
  (matchingMultiplicity d q : ℝ)*(t : ℝ)*
      min (primaryRate q e) (1/(r : ℝ)^f) +
    ((totalMultiplicity d : ℝ)-(matchingMultiplicity d q : ℝ))*(t : ℝ)/(q : ℝ)^e

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

theorem primaryRate_le_one (q a : ℕ) : primaryRate q a ≤ 1 := by
  unfold primaryRate
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^(a*(q-1)))).mpr
  have hh : (((a*(q-1)).choose ((a*(q-1))/2)) : ℝ) ≤ (2 : ℝ)^(a*(q-1)) := by
    exact_mod_cast Nat.choose_le_two_pow (a*(q-1)) ((a*(q-1))/2)
  simpa only [one_mul] using hh

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem genRank_le_two_divisor_rates (hp : P.p = 2) (i : block.Points)
    (q e r f : ℕ) (hq : q.Prime)
    (hqd : q^e ∣ Fintype.card block.Points) (hr : r.Prime)
    (hrd : r^f ∣ Fintype.card block.Points) (hqr : q ≠ r) :
    (MarkedC4.genRank J : ℝ) ≤
      twoDivisorCost (translationDimension J block P)
        (Fintype.card block.Points) q e r f + MarkedC4.genRank block.Top := by
  let t := Fintype.card block.Points
  let d := translationDimension J block P
  let M := Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))
  let weight : ℕ → ℝ := fun p => min (divisorWeight t q e p) (divisorWeight t r f p)
  have ht : 2 ≤ t := by
    simpa only [t,Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hprimary : weight q ≤ (t : ℝ)*min (primaryRate q e) (1/(r : ℝ)^f) := by
    rw [mul_min_of_nonneg _ _ ht0]
    simpa only [weight,divisorRate,if_pos rfl,if_neg hqr,primaryRate,
      div_eq_mul_inv,one_mul] using
      min_le_min (divisorWeight_le_divisorRate t q e q (by omega : 0 < t) hq hqd)
        (divisorWeight_le_divisorRate t r f q (by omega : 0 < t) hr hrd)
  have hother (p : ℕ) (hpq : p ≠ q) : weight p ≤ (t : ℝ)/(q : ℝ)^e := by
    calc
      weight p ≤ divisorWeight t q e p := min_le_left _ _
      _ ≤ divisorRate t q e p := divisorWeight_le_divisorRate t q e p (by omega : 0 < t) hq hqd
      _ = (t : ℝ)/(q : ℝ)^e := by rw [divisorRate,if_neg hpq]
  have hcost := head_weighted_le d M q weight
    ((t : ℝ)*min (primaryRate q e) (1/(r : ℝ)^f)) ((t : ℝ)/(q : ℝ)^e)
    hprimary hother
  have hrank := genRank_le_min_divisorWeights J block P hp i q e r f hq hqd hr hrd
  have hcombined := hrank.trans (add_le_add hcost le_rfl)
  simpa only [twoDivisorCost,totalMultiplicity,matchingMultiplicity,
    Nat.cast_add,Nat.cast_ite,Nat.cast_zero,mul_assoc,mul_div_assoc,d,M,t,weight] using hcombined


theorem genRank_le_single_divisor_rates (hp : P.p = 2) (i : block.Points)
    (q a : ℕ) (hq : q.Prime) (hqd : q^a ∣ Fintype.card block.Points) :
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
      divisorWeight_le_divisorRate t q a q (by omega : 0 < t) hq hqd
  have hother (p : ℕ) (hpq : p ≠ q) : weight p ≤ (t : ℝ)/(q : ℝ)^a := by
    simpa only [weight,divisorRate,if_neg hpq] using
      divisorWeight_le_divisorRate t q a p (by omega : 0 < t) hq hqd
  have hcost := head_weighted_le d M q weight ((t : ℝ)*primaryRate q a)
    ((t : ℝ)/(q : ℝ)^a) hprimary hother
  have hrank := genRank_le_divisorWeight J block P hp i q a hq hqd
  have hcombined := hrank.trans (add_le_add hcost le_rfl)
  simpa only [twoDivisorCost,totalMultiplicity,matchingMultiplicity,
    Nat.cast_add,Nat.cast_ite,Nat.cast_zero,Nat.cast_one,one_pow,div_one,
    min_eq_left (primaryRate_le_one q a),mul_assoc,mul_div_assoc,d,M,t,weight] using hcombined


end SymmetricSubgroupAsymptotics.OriginalBinaryAffineExactChooseDivisorCost
