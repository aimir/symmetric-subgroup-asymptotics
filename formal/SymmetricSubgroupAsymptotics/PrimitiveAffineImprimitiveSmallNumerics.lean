import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveRefinedMargin
import SymmetricSubgroupAsymptotics.RepeatedMarkerProfileBound

/-!
# Numerical budgets for the small affine local degrees

The factorization identities below expose the exact prime coordinates of
the small affine component divisors.  They are kept separate from the block
count case split so the latter can use either Tracey's primary rate or its
prime-power rate without unfolding a `Nat.factorization` expression.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The binary logarithmic slope is exact. -/
theorem logb_two_two_div_two : Real.logb 2 2 / 2 = (1 : ℝ) / 2 := by
  rw [Real.logb_self_eq_one (by norm_num)]

/-- Rational majorant for the prime-five logarithmic slope. -/
theorem logb_two_five_div_five_lt_seven_fifteenths :
    Real.logb 2 5 / 5 < (7 : ℝ) / 15 := by
  have hp : (5 : ℝ) ^ (3 : ℕ) < (2 : ℝ) ^ (7 : ℕ) := by norm_num
  have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < 5 ^ (3 : ℕ)) hp
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlog
  norm_num at hlog ⊢
  nlinarith

/-- Rational majorant for the prime-seven logarithmic slope. -/
theorem logb_two_seven_div_seven_lt_three_sevenths :
    Real.logb 2 7 / 7 < (3 : ℝ) / 7 := by
  have hp : (7 : ℝ) < (2 : ℝ) ^ (3 : ℕ) := by norm_num
  have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 7) hp
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlog
  norm_num at hlog ⊢
  nlinarith

theorem refinedWeightedFactorBudget_two (rate : ℕ → ℝ) :
    refinedWeightedFactorBudget rate 2 = (1 / 2 : ℝ) * rate 2 := by
  rw [show 2 = 2 ^ 1 by norm_num,
    refinedWeightedFactorBudget_prime_pow rate Nat.prime_two]
  norm_num [Real.logb_self_eq_one]

theorem refinedWeightedFactorBudget_six (rate : ℕ → ℝ) :
    refinedWeightedFactorBudget rate 6 =
      (1 / 2 : ℝ) * rate 2 +
        fixedTargetCompositionGamma * rate 3 := by
  rw [show 6 = 2 ^ 1 * 3 ^ 1 by norm_num,
    refinedWeightedFactorBudget_mul rate (by norm_num) (by norm_num),
    refinedWeightedFactorBudget_prime_pow rate Nat.prime_two,
    refinedWeightedFactorBudget_prime_pow rate (by norm_num : Nat.Prime 3)]
  unfold fixedTargetCompositionGamma
  norm_num [Real.logb_self_eq_one]

theorem refinedWeightedFactorBudget_twenty (rate : ℕ → ℝ) :
    refinedWeightedFactorBudget rate 20 =
      rate 2 + (Real.logb 2 5 / 5) * rate 5 := by
  rw [show 20 = 2 ^ 2 * 5 ^ 1 by norm_num,
    refinedWeightedFactorBudget_mul rate (by norm_num) (by norm_num),
    refinedWeightedFactorBudget_prime_pow rate Nat.prime_two,
    refinedWeightedFactorBudget_prime_pow rate (by norm_num : Nat.Prime 5)]
  norm_num [Real.logb_self_eq_one]

theorem refinedWeightedFactorBudget_twentyFour (rate : ℕ → ℝ) :
    refinedWeightedFactorBudget rate 24 =
      (3 / 2 : ℝ) * rate 2 +
        fixedTargetCompositionGamma * rate 3 := by
  rw [show 24 = 2 ^ 3 * 3 ^ 1 by norm_num,
    refinedWeightedFactorBudget_mul rate (by norm_num) (by norm_num),
    refinedWeightedFactorBudget_prime_pow rate Nat.prime_two,
    refinedWeightedFactorBudget_prime_pow rate (by norm_num : Nat.Prime 3)]
  unfold fixedTargetCompositionGamma
  norm_num [Real.logb_self_eq_one]

theorem refinedWeightedFactorBudget_fourThirtyTwo (rate : ℕ → ℝ) :
    refinedWeightedFactorBudget rate 432 =
      2 * rate 2 + 3 * fixedTargetCompositionGamma * rate 3 := by
  rw [show 432 = 2 ^ 4 * 3 ^ 3 by norm_num,
    refinedWeightedFactorBudget_mul rate (by norm_num) (by norm_num),
    refinedWeightedFactorBudget_prime_pow rate Nat.prime_two,
    refinedWeightedFactorBudget_prime_pow rate (by norm_num : Nat.Prime 3)]
  unfold fixedTargetCompositionGamma
  norm_num [Real.logb_self_eq_one]

theorem refinedWeightedFactorBudget_thirteenFortyFour (rate : ℕ → ℝ) :
    refinedWeightedFactorBudget rate 1344 =
      3 * rate 2 + fixedTargetCompositionGamma * rate 3 +
        (Real.logb 2 7 / 7) * rate 7 := by
  rw [show 1344 = (2 ^ 6 * 3 ^ 1) * 7 ^ 1 by norm_num,
    refinedWeightedFactorBudget_mul rate (by norm_num) (by norm_num),
    refinedWeightedFactorBudget_mul rate (by norm_num) (by norm_num),
    refinedWeightedFactorBudget_prime_pow rate Nat.prime_two,
    refinedWeightedFactorBudget_prime_pow rate (by norm_num : Nat.Prime 3),
    refinedWeightedFactorBudget_prime_pow rate (by norm_num : Nat.Prime 7)]
  unfold fixedTargetCompositionGamma
  norm_num [Real.logb_self_eq_one]

/-- Exact factor budget for the soluble degree-eight affine envelope
`8 * 21 = 168`. -/
theorem refinedWeightedFactorBudget_oneSixtyEight (rate : ℕ → ℝ) :
    refinedWeightedFactorBudget rate 168 =
      (3 / 2 : ℝ) * rate 2 +
        fixedTargetCompositionGamma * rate 3 +
        (Real.logb 2 7 / 7) * rate 7 := by
  rw [show 168 = (2 ^ 3 * 3 ^ 1) * 7 ^ 1 by norm_num,
    refinedWeightedFactorBudget_mul rate (by norm_num) (by norm_num),
    refinedWeightedFactorBudget_mul rate (by norm_num) (by norm_num),
    refinedWeightedFactorBudget_prime_pow rate Nat.prime_two,
    refinedWeightedFactorBudget_prime_pow rate (by norm_num : Nat.Prime 3),
    refinedWeightedFactorBudget_prime_pow rate (by norm_num : Nat.Prime 7)]
  unfold fixedTargetCompositionGamma
  norm_num [Real.logb_self_eq_one]

/-- Integral counterpart of the degree-eight soluble envelope. -/
theorem integralRefinedWeightedFactorBudget_oneSixtyEight (rate : ℕ → ℝ) :
    integralRefinedWeightedFactorBudget rate 168 =
      (1 / 2 : ℝ) * (Nat.floor (3 * rate 2) : ℝ) +
        fixedTargetCompositionGamma * (Nat.floor (rate 3) : ℝ) +
        (Real.logb 2 7 / 7) * (Nat.floor (rate 7) : ℝ) := by
  rw [show 168 = (2 ^ 3 * 3 ^ 1) * 7 ^ 1 by norm_num,
    integralRefinedWeightedFactorBudget_mul_of_coprime rate (by decide),
    integralRefinedWeightedFactorBudget_mul_of_coprime rate (by decide),
    integralRefinedWeightedFactorBudget_prime_pow rate Nat.prime_two,
    integralRefinedWeightedFactorBudget_prime_pow rate
      (by norm_num : Nat.Prime 3),
    integralRefinedWeightedFactorBudget_prime_pow rate
      (by norm_num : Nat.Prime 7)]
  unfold fixedTargetCompositionGamma
  norm_num [Real.logb_self_eq_one]

/-- Exact factor budget for the common soluble degree-sixteen affine
envelope `16 * 360 = 5760`. -/
theorem refinedWeightedFactorBudget_fiveSevenSixty (rate : ℕ → ℝ) :
    refinedWeightedFactorBudget rate 5760 =
      (7 / 2 : ℝ) * rate 2 +
        2 * fixedTargetCompositionGamma * rate 3 +
        (Real.logb 2 5 / 5) * rate 5 := by
  rw [show 5760 = (2 ^ 7 * 3 ^ 2) * 5 ^ 1 by norm_num,
    refinedWeightedFactorBudget_mul rate (by norm_num) (by norm_num),
    refinedWeightedFactorBudget_mul rate (by norm_num) (by norm_num),
    refinedWeightedFactorBudget_prime_pow rate Nat.prime_two,
    refinedWeightedFactorBudget_prime_pow rate (by norm_num : Nat.Prime 3),
    refinedWeightedFactorBudget_prime_pow rate (by norm_num : Nat.Prime 5)]
  unfold fixedTargetCompositionGamma
  norm_num [Real.logb_self_eq_one]

theorem refinedWeightedFactorBudget_threeTwentyTwoFiveSixty
    (rate : ℕ → ℝ) :
    refinedWeightedFactorBudget rate 322560 =
      5 * rate 2 + 2 * fixedTargetCompositionGamma * rate 3 +
        (Real.logb 2 5 / 5) * rate 5 +
        (Real.logb 2 7 / 7) * rate 7 := by
  rw [show 322560 = ((2 ^ 10 * 3 ^ 2) * 5 ^ 1) * 7 ^ 1 by norm_num,
    refinedWeightedFactorBudget_mul rate (by norm_num) (by norm_num),
    refinedWeightedFactorBudget_mul rate (by norm_num) (by norm_num),
    refinedWeightedFactorBudget_mul rate (by norm_num) (by norm_num),
    refinedWeightedFactorBudget_prime_pow rate Nat.prime_two,
    refinedWeightedFactorBudget_prime_pow rate (by norm_num : Nat.Prime 3),
    refinedWeightedFactorBudget_prime_pow rate (by norm_num : Nat.Prime 5),
    refinedWeightedFactorBudget_prime_pow rate (by norm_num : Nat.Prime 7)]
  unfold fixedTargetCompositionGamma
  norm_num [Real.logb_self_eq_one]

/-- If the selected primary prime is at least eleven, every prime occurring
in the four small affine overgroup orders uses the prime-to rate. -/
theorem traceyPrimaryRate_le_div_eleven
    (s q e p : ℕ) (hq : q.Prime) (hq11 : 11 ≤ q)
    (he : 1 ≤ e) (hp : p < 11) :
    ActualWreathCompressionTower.traceyPrimaryRate s q e p ≤
      (s : ℝ) / 11 := by
  have hpq : p ≠ q := by omega
  rw [ActualWreathCompressionTower.traceyPrimaryRate, if_neg hpq]
  have hqpow : 11 ≤ q ^ e := by
    calc
      11 ≤ q := hq11
      _ = q ^ 1 := by simp
      _ ≤ q ^ e := Nat.pow_le_pow_right hq.one_le he
  exact div_le_div_of_nonneg_left (by positivity) (by norm_num)
    (by exact_mod_cast hqpow)

theorem traceyPrimaryRate_nonmatching_le
    (s q e p m : ℕ) (hpq : p ≠ q) (hm : m ≤ q ^ e) (hmpos : 0 < m) :
    ActualWreathCompressionTower.traceyPrimaryRate s q e p ≤
      (s : ℝ) / m := by
  rw [ActualWreathCompressionTower.traceyPrimaryRate, if_neg hpq]
  exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hmpos)
    (by exact_mod_cast hm)

theorem traceyPrimaryRate_matching_le
    (s q e : ℕ) (c : ℝ)
    (hroot : Real.sqrt (2 / (3 * ((q : ℝ) - 1) * e)) ≤ c) :
    ActualWreathCompressionTower.traceyPrimaryRate s q e q ≤ (s : ℝ) * c := by
  rw [ActualWreathCompressionTower.traceyPrimaryRate, if_pos rfl]
  exact mul_le_mul_of_nonneg_left hroot (by positivity)

private theorem sqrt_two_over_twelve_e_le_five_twelfths
    (e : ℕ) (he : 1 ≤ e) :
    Real.sqrt (2 / (12 * (e : ℝ))) ≤ (5 : ℝ) / 12 := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num
  · have hden : (12 : ℝ) ≤ 12 * e := by exact_mod_cast (Nat.mul_le_mul_left 12 he)
    have hfrac : (2 : ℝ) / (12 * e) ≤ 2 / 12 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
    norm_num at hfrac ⊢
    nlinarith

private theorem sqrt_two_over_six_e_le_five_twelfths
    (e : ℕ) (he : 2 ≤ e) :
    Real.sqrt (2 / (6 * (e : ℝ))) ≤ (5 : ℝ) / 12 := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num
  · have hden : (12 : ℝ) ≤ 6 * e := by
      have := Nat.mul_le_mul_left 6 he
      norm_num at this ⊢
      exact_mod_cast this
    have hfrac : (2 : ℝ) / (6 * e) ≤ 2 / 12 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
    norm_num at hfrac ⊢
    nlinarith

private theorem sqrt_two_over_eighteen_e_le_one_third
    (e : ℕ) (he : 1 ≤ e) :
    Real.sqrt (2 / (18 * (e : ℝ))) ≤ (1 : ℝ) / 3 := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num
  · have hden : (18 : ℝ) ≤ 18 * e := by exact_mod_cast (Nat.mul_le_mul_left 18 he)
    have hfrac : (2 : ℝ) / (18 * e) ≤ 2 / 18 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
    norm_num at hfrac ⊢
    exact hfrac

private theorem sqrt_two_over_three_e_le_three_eighths
    (e : ℕ) (he : 5 ≤ e) :
    Real.sqrt (2 / (3 * (e : ℝ))) ≤ (3 : ℝ) / 8 := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num
  · have hden : (15 : ℝ) ≤ 3 * e := by exact_mod_cast (Nat.mul_le_mul_left 3 he)
    have hfrac : (2 : ℝ) / (3 * e) ≤ 2 / 15 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
    norm_num at hfrac ⊢
    nlinarith

private theorem sqrt_two_over_three_e_le_five_twelfths
    (e : ℕ) (he : 4 ≤ e) :
    Real.sqrt (2 / (3 * (e : ℝ))) ≤ (5 : ℝ) / 12 := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num
  · have hden : (12 : ℝ) ≤ 3 * e := by exact_mod_cast (Nat.mul_le_mul_left 3 he)
    have hfrac : (2 : ℝ) / (3 * e) ≤ 2 / 12 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
    norm_num at hfrac ⊢
    nlinarith

theorem traceyPrimaryRate_five_matching
    (s e : ℕ) (he : 1 ≤ e) :
    ActualWreathCompressionTower.traceyPrimaryRate s 5 e 5 ≤
      (s : ℝ) * (5 / 12 : ℝ) := by
  apply traceyPrimaryRate_matching_le
  convert sqrt_two_over_twelve_e_le_five_twelfths e he using 1 <;> norm_num

theorem traceyPrimaryRate_three_matching_of_two_le
    (s e : ℕ) (he : 2 ≤ e) :
    ActualWreathCompressionTower.traceyPrimaryRate s 3 e 3 ≤
      (s : ℝ) * (5 / 12 : ℝ) := by
  apply traceyPrimaryRate_matching_le
  convert sqrt_two_over_six_e_le_five_twelfths e he using 1 <;> norm_num

theorem traceyPrimaryRate_seven_matching
    (s e : ℕ) (he : 1 ≤ e) :
    ActualWreathCompressionTower.traceyPrimaryRate s 7 e 7 ≤
      (s : ℝ) / 3 := by
  convert traceyPrimaryRate_matching_le s 7 e (1 / 3 : ℝ)
      (by convert sqrt_two_over_eighteen_e_le_one_third e he using 1 <;> norm_num)
    using 1 <;> ring

theorem traceyPrimaryRate_two_matching_of_five_le
    (s e : ℕ) (he : 5 ≤ e) :
    ActualWreathCompressionTower.traceyPrimaryRate s 2 e 2 ≤
      (s : ℝ) * (3 / 8 : ℝ) := by
  apply traceyPrimaryRate_matching_le
  convert sqrt_two_over_three_e_le_three_eighths e he using 1 <;> norm_num

theorem traceyPrimaryRate_two_matching_of_four_le
    (s e : ℕ) (he : 4 ≤ e) :
    ActualWreathCompressionTower.traceyPrimaryRate s 2 e 2 ≤
      (s : ℝ) * (5 / 12 : ℝ) := by
  apply traceyPrimaryRate_matching_le
  convert sqrt_two_over_three_e_le_five_twelfths e he using 1 <;> norm_num

theorem refinedWeightedFactorBudget_twenty_le_of_rate_le
    (rate : ℕ → ℝ) (x : ℝ)
    (h2 : rate 2 ≤ x) (h5 : rate 5 ≤ x)
    (hr5 : 0 ≤ rate 5) :
    refinedWeightedFactorBudget rate 20 ≤ (22 / 15 : ℝ) * x := by
  rw [refinedWeightedFactorBudget_twenty]
  have hfive := logb_two_five_div_five_lt_seven_fifteenths.le
  have hfive0 : 0 ≤ Real.logb 2 5 / 5 :=
    div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)
  calc
    rate 2 + Real.logb 2 5 / 5 * rate 5 ≤
        x + (7 / 15 : ℝ) * rate 5 := by
      gcongr
    _ ≤ x + (7 / 15 : ℝ) * x := by gcongr
    _ = (22 / 15 : ℝ) * x := by ring

theorem refinedWeightedFactorBudget_thirteenFortyFour_le_of_rate_le
    (rate : ℕ → ℝ) (x : ℝ)
    (h2 : rate 2 ≤ x) (h3 : rate 3 ≤ x) (h7 : rate 7 ≤ x)
    (hr3 : 0 ≤ rate 3) (hr7 : 0 ≤ rate 7) :
    refinedWeightedFactorBudget rate 1344 ≤ (887 / 224 : ℝ) * x := by
  rw [refinedWeightedFactorBudget_thirteenFortyFour]
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hseven := logb_two_seven_div_seven_lt_three_sevenths.le
  have hgamma0 : 0 ≤ fixedTargetCompositionGamma := by
    unfold fixedTargetCompositionGamma
    exact div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)
  have hseven0 : 0 ≤ Real.logb 2 7 / 7 :=
    div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)
  calc
    3 * rate 2 + fixedTargetCompositionGamma * rate 3 +
          Real.logb 2 7 / 7 * rate 7 ≤
        3 * x + (17 / 32 : ℝ) * rate 3 +
          (3 / 7 : ℝ) * rate 7 := by gcongr
    _ ≤ 3 * x + (17 / 32 : ℝ) * x + (3 / 7 : ℝ) * x := by
      gcongr
    _ = (887 / 224 : ℝ) * x := by ring

theorem refinedWeightedFactorBudget_fourThirtyTwo_le_of_rate_le
    (rate : ℕ → ℝ) (x : ℝ)
    (h2 : rate 2 ≤ x) (h3 : rate 3 ≤ x)
    (hr3 : 0 ≤ rate 3) :
    refinedWeightedFactorBudget rate 432 ≤ (115 / 32 : ℝ) * x := by
  rw [refinedWeightedFactorBudget_fourThirtyTwo]
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hgamma0 : 0 ≤ fixedTargetCompositionGamma := by
    unfold fixedTargetCompositionGamma
    exact div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)
  calc
    2 * rate 2 + 3 * fixedTargetCompositionGamma * rate 3 ≤
        2 * x + 3 * (17 / 32 : ℝ) * rate 3 := by gcongr
    _ ≤ 2 * x + 3 * (17 / 32 : ℝ) * x := by gcongr
    _ = (115 / 32 : ℝ) * x := by ring

theorem refinedWeightedFactorBudget_threeTwentyTwoFiveSixty_le_of_rate_le
    (rate : ℕ → ℝ) (x : ℝ)
    (h2 : rate 2 ≤ x) (h3 : rate 3 ≤ x)
    (h5 : rate 5 ≤ x) (h7 : rate 7 ≤ x)
    (hr3 : 0 ≤ rate 3)
    (hr5 : 0 ≤ rate 5) (hr7 : 0 ≤ rate 7) :
    refinedWeightedFactorBudget rate 322560 ≤ (11689 / 1680 : ℝ) * x := by
  rw [refinedWeightedFactorBudget_threeTwentyTwoFiveSixty]
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hfive := logb_two_five_div_five_lt_seven_fifteenths.le
  have hseven := logb_two_seven_div_seven_lt_three_sevenths.le
  have hgamma0 : 0 ≤ fixedTargetCompositionGamma := by
    unfold fixedTargetCompositionGamma
    exact div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)
  have hfive0 : 0 ≤ Real.logb 2 5 / 5 :=
    div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)
  have hseven0 : 0 ≤ Real.logb 2 7 / 7 :=
    div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)
  calc
    5 * rate 2 + 2 * fixedTargetCompositionGamma * rate 3 +
          Real.logb 2 5 / 5 * rate 5 + Real.logb 2 7 / 7 * rate 7 ≤
        5 * x + 2 * (17 / 32 : ℝ) * rate 3 +
          (7 / 15 : ℝ) * rate 5 + (3 / 7 : ℝ) * rate 7 := by gcongr
    _ ≤ 5 * x + 2 * (17 / 32 : ℝ) * x +
          (7 / 15 : ℝ) * x + (3 / 7 : ℝ) * x := by gcongr
    _ = (11689 / 1680 : ℝ) * x := by ring

/-- The common arithmetic at a block-count prime divisor at least eleven.
The one-point parity loss for odd local degree is retained explicitly. -/
theorem smallAffine_largePrime_margin
    (r s w : ℕ) (hs : 2 ≤ s) (hw : w = r * s)
    (c eta : ℝ)
    (hrc : (r = 5 ∧ c = 22 / 15) ∨
      (r = 8 ∧ c = 887 / 224) ∨
      (r = 9 ∧ c = 115 / 32) ∨
      (r = 16 ∧ c = 11689 / 1680))
    (heta : eta ≤ c * ((s : ℝ) / 11)) :
    Non2UnipotentPrefixFiniteMenu.preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - s) / 8 - eta := by
  have heven : (w : ℝ) ≤ evenWidth w + 1 := by
    exact_mod_cast width_le_evenWidth_add_one w
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hwR : (w : ℝ) = r * s := by exact_mod_cast hw
  unfold Non2UnipotentPrefixFiniteMenu.preE7CharacterRho
  rcases hrc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hc : (1 / 8192 : ℝ) * 5 +
        (22 / 15) * (1 / 11) + 1 / 16 ≤ 4 / 8 := by norm_num
    have hcS := mul_le_mul_of_nonneg_right hc (show (0 : ℝ) ≤ s by positivity)
    rw [hwR] at heven ⊢
    norm_num [div_eq_mul_inv] at hcS heta ⊢
    ring_nf at heven hcS heta ⊢
    nlinarith
  · have hc : (1 / 8192 : ℝ) * 8 +
        (887 / 224) * (1 / 11) + 1 / 16 ≤ 7 / 8 := by norm_num
    have hcS := mul_le_mul_of_nonneg_right hc (show (0 : ℝ) ≤ s by positivity)
    rw [hwR] at heven ⊢
    norm_num [div_eq_mul_inv] at hcS heta ⊢
    ring_nf at heven hcS heta ⊢
    nlinarith
  · have hc : (1 / 8192 : ℝ) * 9 +
        (115 / 32) * (1 / 11) + 1 / 16 ≤ 8 / 8 := by norm_num
    have hcS := mul_le_mul_of_nonneg_right hc (show (0 : ℝ) ≤ s by positivity)
    rw [hwR] at heven ⊢
    norm_num [div_eq_mul_inv] at hcS heta ⊢
    ring_nf at heven hcS heta ⊢
    nlinarith
  · have hc : (1 / 8192 : ℝ) * 16 +
        (11689 / 1680) * (1 / 11) + 1 / 16 ≤ 15 / 8 := by norm_num
    have hcS := mul_le_mul_of_nonneg_right hc (show (0 : ℝ) ≤ s by positivity)
    rw [hwR] at heven ⊢
    norm_num [div_eq_mul_inv] at hcS heta ⊢
    ring_nf at heven hcS heta ⊢
    nlinarith

theorem refinedBudget_twenty_traceyPrimary_largePrime
    (s q e : ℕ) (hq : q.Prime) (hq11 : 11 ≤ q) (he : 1 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate s q e) 20 ≤
      (22 / 15 : ℝ) * ((s : ℝ) / 11) := by
  apply refinedWeightedFactorBudget_twenty_le_of_rate_le
  · exact traceyPrimaryRate_le_div_eleven s q e 2 hq hq11 he (by norm_num)
  · exact traceyPrimaryRate_le_div_eleven s q e 5 hq hq11 he (by norm_num)
  · exact ActualWreathCompressionTower.traceyPrimaryRate_nonneg s q e 5

theorem refinedBudget_thirteenFortyFour_traceyPrimary_largePrime
    (s q e : ℕ) (hq : q.Prime) (hq11 : 11 ≤ q) (he : 1 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate s q e) 1344 ≤
      (887 / 224 : ℝ) * ((s : ℝ) / 11) := by
  apply refinedWeightedFactorBudget_thirteenFortyFour_le_of_rate_le
  · exact traceyPrimaryRate_le_div_eleven s q e 2 hq hq11 he (by norm_num)
  · exact traceyPrimaryRate_le_div_eleven s q e 3 hq hq11 he (by norm_num)
  · exact traceyPrimaryRate_le_div_eleven s q e 7 hq hq11 he (by norm_num)
  · exact ActualWreathCompressionTower.traceyPrimaryRate_nonneg s q e 3
  · exact ActualWreathCompressionTower.traceyPrimaryRate_nonneg s q e 7

theorem refinedBudget_fourThirtyTwo_traceyPrimary_largePrime
    (s q e : ℕ) (hq : q.Prime) (hq11 : 11 ≤ q) (he : 1 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate s q e) 432 ≤
      (115 / 32 : ℝ) * ((s : ℝ) / 11) := by
  apply refinedWeightedFactorBudget_fourThirtyTwo_le_of_rate_le
  · exact traceyPrimaryRate_le_div_eleven s q e 2 hq hq11 he (by norm_num)
  · exact traceyPrimaryRate_le_div_eleven s q e 3 hq hq11 he (by norm_num)
  · exact ActualWreathCompressionTower.traceyPrimaryRate_nonneg s q e 3

theorem refinedBudget_threeTwentyTwoFiveSixty_traceyPrimary_largePrime
    (s q e : ℕ) (hq : q.Prime) (hq11 : 11 ≤ q) (he : 1 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate s q e) 322560 ≤
      (11689 / 1680 : ℝ) * ((s : ℝ) / 11) := by
  apply refinedWeightedFactorBudget_threeTwentyTwoFiveSixty_le_of_rate_le
  · exact traceyPrimaryRate_le_div_eleven s q e 2 hq hq11 he (by norm_num)
  · exact traceyPrimaryRate_le_div_eleven s q e 3 hq hq11 he (by norm_num)
  · exact traceyPrimaryRate_le_div_eleven s q e 5 hq hq11 he (by norm_num)
  · exact traceyPrimaryRate_le_div_eleven s q e 7 hq hq11 he (by norm_num)
  · exact ActualWreathCompressionTower.traceyPrimaryRate_nonneg s q e 3
  · exact ActualWreathCompressionTower.traceyPrimaryRate_nonneg s q e 5
  · exact ActualWreathCompressionTower.traceyPrimaryRate_nonneg s q e 7

end SymmetricSubgroupAsymptotics

end
