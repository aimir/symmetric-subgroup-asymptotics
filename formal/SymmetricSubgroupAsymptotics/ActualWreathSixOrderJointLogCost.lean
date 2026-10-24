import SymmetricSubgroupAsymptotics.ActualWreathUnitDivisorWeightBudget
import SymmetricSubgroupAsymptotics.ActualWreathSixOrderChooseCost
import SymmetricSubgroupAsymptotics.LargestPrimePowerQuadraticEntropy
import Mathlib.Tactic.IntervalCases

/-! A single ACTUAL order-six chief cost has simultaneous joint bounds:
8/5 times the unit logarithmic rate, and half the block degree when the
largest primary divisor is at least8. Distinct defining characteristics
cannot both saturate their primary rates at the same original degree.
No group is replaced by independent coordinate factors. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathSixOrderJointLogCost
open ActualWreathChiefWeightedPrimeBudget ActualWreathChooseDivisorCapacity
open ActualWreathOrdinaryChiefRecurrence

private theorem normalized_le_three_eighths (b : ℕ) (hb : 3 ≤ b) :
    (b.choose (b/2) : ℝ)/(2 : ℝ)^b ≤ 3/8 := by
  have hh := CentralBinomialNormalizedAntitone.normalized_antitone hb
  norm_num at hh
  exact hh

private theorem binary_rate_le (a : ℕ) (hM : 8 ≤ 2^a) : primaryRate 2 a ≤ 3/8 := by
  have ha : 3 ≤ a := by
    by_contra hn
    have ha' : a ≤ 2 := by omega
    interval_cases a <;> norm_num at hM
  simpa only [primaryRate,Nat.reduceSub,mul_one] using normalized_le_three_eighths a ha

private theorem ternary_rate_le (a : ℕ) (hM : 8 ≤ 3^a) : primaryRate 3 a ≤ 3/8 := by
  have ha : 2 ≤ a := by
    by_contra hn
    have ha' : a ≤ 1 := by omega
    interval_cases a <;> norm_num at hM
  exact normalized_le_three_eighths (a*(3-1)) (by omega)

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]
    (S : ActualWreathCompressionState Q I)

theorem exists_cost (i : I) (hI : 2 ≤ Fintype.card I)
    (horder : Nat.card S.D ∣ 6) (q a : ℕ) (hq : q.Prime)
    (hdiv : q^a ∣ Fintype.card I)
    (hmax : ∀ p ∈ (Fintype.card I).primeFactors,
      p^(Fintype.card I).factorization p ≤ q^a) :
    ∃ c : ℕ, ChiefCost i S c ∧ MarkedC4.genRank S.A ≤ c+MarkedC4.genRank Q ∧
      (c : ℝ) ≤ (8/5)*(Fintype.card I : ℝ)/
        Real.sqrt (Real.logb 2 (Fintype.card I : ℝ)) ∧
      (8 ≤ q^a → (c : ℝ) ≤ (Fintype.card I : ℝ)/2) := by
  let t := Fintype.card I
  let M := q^a
  let V : ℝ := (t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))
  let W : ℕ → ℝ := ActualWreathUnitDivisorWeightBudget.weight t q a
  have ht : 2 ≤ t := hI
  have ht0 : 0 < t := by omega
  have htR : (0 : ℝ) ≤ t := by positivity
  have hM1 : 1 ≤ M := Nat.one_le_pow _ _ hq.pos
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hw1 (p : ℕ) : 1 ≤ W p :=
    ActualWreathUnitDivisorWeightBudget.one_le_weight t ht q a p
  have hwU (p : ℕ) : W p ≤ V := min_le_left _ _
  have hwD (p : ℕ) : W p ≤ divisorRate t q a p :=
    (min_le_right _ _).trans (divisorWeight_le_divisorRate t q a p ht0 hq hdiv)
  have hwOther (p : ℕ) (hp : p ≠ q) : W p ≤ (t : ℝ)/(M : ℝ) := by
    have hh := hwD p
    simpa only [divisorRate,if_neg hp,M,Nat.cast_pow] using hh
  have hwPrimary : W q ≤ (t : ℝ)*primaryRate q a := by
    simpa only [divisorRate,if_pos rfl] using hwD q
  have hrec : (t : ℝ)/(M : ℝ) ≤ (3/5)*V := by
    simpa only [V,mul_div_assoc] using
      LargestPrimePowerQuadraticEntropy.reciprocal_rate_le_three_fifths t M ht hM1 hmax
  have hsumLog : W 2+W 3 ≤ (8/5)*V := by
    by_cases hq2 : q = 2
    · have h3 := (hwOther 3 (by omega)).trans hrec
      linarith only [hwU 2,h3]
    · by_cases hq3 : q = 3
      · have h2 := (hwOther 2 (by omega)).trans hrec
        linarith only [hwU 3,h2]
      · have h2 := (hwOther 2 (Ne.symm hq2)).trans hrec
        have h3 := (hwOther 3 (Ne.symm hq3)).trans hrec
        linarith only [h2,h3,hV]
  have hsumHalf (hM8 : 8 ≤ M) : W 2+W 3 ≤ (t : ℝ)/2 := by
    have hM8R : (8 : ℝ) ≤ M := by exact_mod_cast hM8
    have hrec8 : (t : ℝ)/(M : ℝ) ≤ (t : ℝ)/8 := by
      apply (div_le_iff₀ hMpos).mpr
      have hh := mul_le_mul_of_nonneg_left hM8R htR
      nlinarith only [hh]
    by_cases hq2 : q = 2
    · have hr := binary_rate_le a (by simpa only [M,hq2] using hM8)
      have h2 : W 2 ≤ (t : ℝ)*(3/8) := by
        have hh : W 2 ≤ (t : ℝ)*primaryRate 2 a := by simpa only [hq2] using hwPrimary
        exact hh.trans (mul_le_mul_of_nonneg_left hr htR)
      have h3 := (hwOther 3 (by omega)).trans hrec8
      linarith only [h2,h3]
    · by_cases hq3 : q = 3
      · have hr := ternary_rate_le a (by simpa only [M,hq3] using hM8)
        have h3 : W 3 ≤ (t : ℝ)*(3/8) := by
          have hh : W 3 ≤ (t : ℝ)*primaryRate 3 a := by simpa only [hq3] using hwPrimary
          exact hh.trans (mul_le_mul_of_nonneg_left hr htR)
        have h2 := (hwOther 2 (by omega)).trans hrec8
        linarith only [h2,h3]
      · have h2 := (hwOther 2 (Ne.symm hq2)).trans hrec8
        have h3 := (hwOther 3 (Ne.symm hq3)).trans hrec8
        linarith only [h2,h3,htR]
  obtain ⟨c,hc⟩ := ActualWreathOrdinaryChiefRecurrence.exists_chiefCost i S
  have hcost := ActualWreathUnitDivisorWeightBudget.cost_le_weightedOrder hc hI q a hq hdiv
  have hlocal := weightedOrder_mono_of_dvd W
    (fun p => (show (0 : ℝ) ≤ 1 by norm_num).trans (hw1 p))
    (Nat.card_pos (α := S.D)).ne' (by norm_num : (6 : ℕ) ≠ 0) horder
  rw [ActualWreathSixOrderChooseCost.weightedOrder_six] at hlocal
  have hcSum : (c : ℝ) ≤ W 2+W 3 := hcost.trans hlocal
  refine ⟨c,hc,genRank_le_cost_add_top hc,?_,?_⟩
  · have hh := hcSum.trans hsumLog
    convert hh using 1 <;> dsimp only [V,t] <;> ring
  · intro hM8
    exact hcSum.trans (hsumHalf hM8)

end SymmetricSubgroupAsymptotics.ActualWreathSixOrderJointLogCost
