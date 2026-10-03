import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallNumerics

/-!
# Refined small-prime budgets for small affine components

The exact factorization formulae from
`PrimitiveAffineImprimitiveSmallNumerics` are combined here with the sharp
primary Tracey rate.  These are the finite numerical inequalities for block
counts divisible by `5`, `7`, `3^2`, or by the indicated binary power.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

private theorem rate_nonneg (s q e p : ℕ) :
    0 ≤ ActualWreathCompressionTower.traceyPrimaryRate s q e p :=
  ActualWreathCompressionTower.traceyPrimaryRate_nonneg s q e p

private theorem gamma_nonneg : 0 ≤ fixedTargetCompositionGamma := by
  unfold fixedTargetCompositionGamma
  exact div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)

private theorem slope_five_nonneg : 0 ≤ Real.logb 2 5 / 5 := by
  exact div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)

private theorem slope_seven_nonneg : 0 ≤ Real.logb 2 7 / 7 := by
  exact div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)

private theorem five_le_pow (e : ℕ) (he : 1 ≤ e) : 5 ≤ 5 ^ e := by
  calc
    5 = 5 ^ 1 := by norm_num
    _ ≤ 5 ^ e := Nat.pow_le_pow_right (by norm_num : 0 < 5) he

private theorem seven_le_pow (e : ℕ) (he : 1 ≤ e) : 7 ≤ 7 ^ e := by
  calc
    7 = 7 ^ 1 := by norm_num
    _ ≤ 7 ^ e := Nat.pow_le_pow_right (by norm_num : 0 < 7) he

/-! ## Selected prime five -/

theorem refinedBudget_twenty_traceyPrimary_five
    (s e : ℕ) (he : 1 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate s 5 e) 20 ≤
      (71 / 180 : ℝ) * s := by
  rw [refinedWeightedFactorBudget_twenty]
  have h2 := traceyPrimaryRate_nonmatching_le s 5 e 2 5 (by norm_num)
    (five_le_pow e he) (by norm_num)
  have h5 := traceyPrimaryRate_five_matching s e he
  have hslope := logb_two_five_div_five_lt_seven_fifteenths.le
  have hr5 := rate_nonneg s 5 e 5
  norm_num at h2
  calc
    _ ≤ (s : ℝ) / 5 + (7 / 15 : ℝ) *
          ActualWreathCompressionTower.traceyPrimaryRate s 5 e 5 := by gcongr
    _ ≤ (s : ℝ) / 5 + (7 / 15 : ℝ) * ((s : ℝ) * (5 / 12)) := by gcongr
    _ = (71 / 180 : ℝ) * s := by ring

theorem refinedBudget_thirteenFortyFour_traceyPrimary_five
    (s e : ℕ) (he : 1 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate s 5 e) 1344 ≤
      (887 / 1120 : ℝ) * s := by
  have h := refinedWeightedFactorBudget_thirteenFortyFour_le_of_rate_le
      (ActualWreathCompressionTower.traceyPrimaryRate s 5 e) ((s : ℝ) / 5)
      (traceyPrimaryRate_nonmatching_le s 5 e 2 5 (by norm_num)
        (five_le_pow e he) (by norm_num))
      (traceyPrimaryRate_nonmatching_le s 5 e 3 5 (by norm_num)
        (five_le_pow e he) (by norm_num))
      (traceyPrimaryRate_nonmatching_le s 5 e 7 5 (by norm_num)
        (five_le_pow e he) (by norm_num))
      (rate_nonneg s 5 e 3) (rate_nonneg s 5 e 7)
  convert h using 1 <;> ring

theorem refinedBudget_fourThirtyTwo_traceyPrimary_five
    (s e : ℕ) (he : 1 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate s 5 e) 432 ≤
      (23 / 32 : ℝ) * s := by
  have h := refinedWeightedFactorBudget_fourThirtyTwo_le_of_rate_le
    (ActualWreathCompressionTower.traceyPrimaryRate s 5 e) ((s : ℝ) / 5)
    (traceyPrimaryRate_nonmatching_le s 5 e 2 5 (by norm_num)
      (five_le_pow e he) (by norm_num))
    (traceyPrimaryRate_nonmatching_le s 5 e 3 5 (by norm_num)
      (five_le_pow e he) (by norm_num))
    (rate_nonneg s 5 e 3)
  convert h using 1 <;> ring

theorem refinedBudget_threeTwentyTwoFiveSixty_traceyPrimary_five
    (s e : ℕ) (he : 1 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate s 5 e) 322560 ≤
      (7523 / 5040 : ℝ) * s := by
  rw [refinedWeightedFactorBudget_threeTwentyTwoFiveSixty]
  have h2 := traceyPrimaryRate_nonmatching_le s 5 e 2 5 (by norm_num)
    (five_le_pow e he) (by norm_num)
  have h3 := traceyPrimaryRate_nonmatching_le s 5 e 3 5 (by norm_num)
    (five_le_pow e he) (by norm_num)
  have h5 := traceyPrimaryRate_five_matching s e he
  have h7 := traceyPrimaryRate_nonmatching_le s 5 e 7 5 (by norm_num)
    (five_le_pow e he) (by norm_num)
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hslope5 := logb_two_five_div_five_lt_seven_fifteenths.le
  have hslope7 := logb_two_seven_div_seven_lt_three_sevenths.le
  have hr3 := rate_nonneg s 5 e 3
  have hr5 := rate_nonneg s 5 e 5
  have hr7 := rate_nonneg s 5 e 7
  norm_num at h2 h3 h7
  calc
    _ ≤ 5 * ((s : ℝ) / 5) + 2 * (17 / 32 : ℝ) * ((s : ℝ) / 5) +
          (7 / 15 : ℝ) * ((s : ℝ) * (5 / 12)) +
          (3 / 7 : ℝ) * ((s : ℝ) / 5) := by
      gcongr
    _ = (7523 / 5040 : ℝ) * s := by ring

/-! ## Selected prime seven -/

theorem refinedBudget_twenty_traceyPrimary_seven
    (s e : ℕ) (he : 1 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate s 7 e) 20 ≤
      (22 / 105 : ℝ) * s := by
  have h := refinedWeightedFactorBudget_twenty_le_of_rate_le
    (ActualWreathCompressionTower.traceyPrimaryRate s 7 e) ((s : ℝ) / 7)
    (traceyPrimaryRate_nonmatching_le s 7 e 2 7 (by norm_num)
      (seven_le_pow e he) (by norm_num))
    (traceyPrimaryRate_nonmatching_le s 7 e 5 7 (by norm_num)
      (seven_le_pow e he) (by norm_num))
    (rate_nonneg s 7 e 5)
  convert h using 1 <;> ring

theorem refinedBudget_thirteenFortyFour_traceyPrimary_seven
    (s e : ℕ) (he : 1 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate s 7 e) 1344 ≤
      (145 / 224 : ℝ) * s := by
  rw [refinedWeightedFactorBudget_thirteenFortyFour]
  have h2 := traceyPrimaryRate_nonmatching_le s 7 e 2 7 (by norm_num)
    (seven_le_pow e he) (by norm_num)
  have h3 := traceyPrimaryRate_nonmatching_le s 7 e 3 7 (by norm_num)
    (seven_le_pow e he) (by norm_num)
  have h7 := traceyPrimaryRate_seven_matching s e he
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hslope7 := logb_two_seven_div_seven_lt_three_sevenths.le
  have hr3 := rate_nonneg s 7 e 3
  have hr7 := rate_nonneg s 7 e 7
  norm_num at h2 h3
  calc
    _ ≤ 3 * ((s : ℝ) / 7) + (17 / 32 : ℝ) * ((s : ℝ) / 7) +
          (3 / 7 : ℝ) * ((s : ℝ) / 3) := by gcongr
    _ = (145 / 224 : ℝ) * s := by ring

theorem refinedBudget_fourThirtyTwo_traceyPrimary_seven
    (s e : ℕ) (he : 1 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate s 7 e) 432 ≤
      (115 / 224 : ℝ) * s := by
  have h := refinedWeightedFactorBudget_fourThirtyTwo_le_of_rate_le
    (ActualWreathCompressionTower.traceyPrimaryRate s 7 e) ((s : ℝ) / 7)
    (traceyPrimaryRate_nonmatching_le s 7 e 2 7 (by norm_num)
      (seven_le_pow e he) (by norm_num))
    (traceyPrimaryRate_nonmatching_le s 7 e 3 7 (by norm_num)
      (seven_le_pow e he) (by norm_num))
    (rate_nonneg s 7 e 3)
  convert h using 1 <;> ring

theorem refinedBudget_threeTwentyTwoFiveSixty_traceyPrimary_seven
    (s e : ℕ) (he : 1 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate s 7 e) 322560 ≤
      (1807 / 1680 : ℝ) * s := by
  rw [refinedWeightedFactorBudget_threeTwentyTwoFiveSixty]
  have h2 := traceyPrimaryRate_nonmatching_le s 7 e 2 7 (by norm_num)
    (seven_le_pow e he) (by norm_num)
  have h3 := traceyPrimaryRate_nonmatching_le s 7 e 3 7 (by norm_num)
    (seven_le_pow e he) (by norm_num)
  have h5 := traceyPrimaryRate_nonmatching_le s 7 e 5 7 (by norm_num)
    (seven_le_pow e he) (by norm_num)
  have h7 := traceyPrimaryRate_seven_matching s e he
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hslope5 := logb_two_five_div_five_lt_seven_fifteenths.le
  have hslope7 := logb_two_seven_div_seven_lt_three_sevenths.le
  have hr3 := rate_nonneg s 7 e 3
  have hr5 := rate_nonneg s 7 e 5
  have hr7 := rate_nonneg s 7 e 7
  norm_num at h2 h3 h5
  calc
    _ ≤ 5 * ((s : ℝ) / 7) + 2 * (17 / 32 : ℝ) * ((s : ℝ) / 7) +
          (7 / 15 : ℝ) * ((s : ℝ) / 7) +
          (3 / 7 : ℝ) * ((s : ℝ) / 3) := by gcongr
    _ = (1807 / 1680 : ℝ) * s := by ring

/-! ## Selected prime three, exponent at least two -/

theorem refinedBudget_twenty_traceyPrimary_three
    (s e : ℕ) (he : 2 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate s 3 e) 20 ≤
      (22 / 135 : ℝ) * s := by
  have hpow : 9 ≤ 3 ^ e := by
    exact (show 3 ^ 2 ≤ 3 ^ e from
      Nat.pow_le_pow_right (by norm_num : 0 < 3) he)
  have h := refinedWeightedFactorBudget_twenty_le_of_rate_le
    (ActualWreathCompressionTower.traceyPrimaryRate s 3 e) ((s : ℝ) / 9)
    (traceyPrimaryRate_nonmatching_le s 3 e 2 9 (by norm_num) hpow (by norm_num))
    (traceyPrimaryRate_nonmatching_le s 3 e 5 9 (by norm_num) hpow (by norm_num))
    (rate_nonneg s 3 e 5)
  convert h using 1 <;> ring

theorem refinedBudget_thirteenFortyFour_traceyPrimary_three
    (s e : ℕ) (he : 2 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate s 3 e) 1344 ≤
      (1619 / 2688 : ℝ) * s := by
  rw [refinedWeightedFactorBudget_thirteenFortyFour]
  have hpow : 9 ≤ 3 ^ e :=
    Nat.pow_le_pow_right (by norm_num : 0 < 3) he
  have h2 := traceyPrimaryRate_nonmatching_le s 3 e 2 9 (by norm_num) hpow (by norm_num)
  have h3 := traceyPrimaryRate_three_matching_of_two_le s e he
  have h7 := traceyPrimaryRate_nonmatching_le s 3 e 7 9 (by norm_num) hpow (by norm_num)
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hslope7 := logb_two_seven_div_seven_lt_three_sevenths.le
  have hr3 := rate_nonneg s 3 e 3
  have hr7 := rate_nonneg s 3 e 7
  norm_num at h2 h7
  calc
    _ ≤ 3 * ((s : ℝ) / 9) + (17 / 32 : ℝ) * ((s : ℝ) * (5 / 12)) +
          (3 / 7 : ℝ) * ((s : ℝ) / 9) := by gcongr
    _ = (1619 / 2688 : ℝ) * s := by ring

theorem refinedBudget_fourThirtyTwo_traceyPrimary_three
    (s e : ℕ) (he : 2 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate s 3 e) 432 ≤
      (1021 / 1152 : ℝ) * s := by
  rw [refinedWeightedFactorBudget_fourThirtyTwo]
  have hpow : 9 ≤ 3 ^ e :=
    Nat.pow_le_pow_right (by norm_num : 0 < 3) he
  have h2 := traceyPrimaryRate_nonmatching_le s 3 e 2 9 (by norm_num) hpow (by norm_num)
  have h3 := traceyPrimaryRate_three_matching_of_two_le s e he
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hr3 := rate_nonneg s 3 e 3
  norm_num at h2
  calc
    _ ≤ 2 * ((s : ℝ) / 9) + 3 * (17 / 32 : ℝ) *
          ((s : ℝ) * (5 / 12)) := by gcongr
    _ = (1021 / 1152 : ℝ) * s := by ring

theorem refinedBudget_threeTwentyTwoFiveSixty_traceyPrimary_three
    (s e : ℕ) (he : 2 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate s 3 e) 322560 ≤
      (66391 / 60480 : ℝ) * s := by
  rw [refinedWeightedFactorBudget_threeTwentyTwoFiveSixty]
  have hpow : 9 ≤ 3 ^ e :=
    Nat.pow_le_pow_right (by norm_num : 0 < 3) he
  have h2 := traceyPrimaryRate_nonmatching_le s 3 e 2 9 (by norm_num) hpow (by norm_num)
  have h3 := traceyPrimaryRate_three_matching_of_two_le s e he
  have h5 := traceyPrimaryRate_nonmatching_le s 3 e 5 9 (by norm_num) hpow (by norm_num)
  have h7 := traceyPrimaryRate_nonmatching_le s 3 e 7 9 (by norm_num) hpow (by norm_num)
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hslope5 := logb_two_five_div_five_lt_seven_fifteenths.le
  have hslope7 := logb_two_seven_div_seven_lt_three_sevenths.le
  have hr3 := rate_nonneg s 3 e 3
  have hr5 := rate_nonneg s 3 e 5
  have hr7 := rate_nonneg s 3 e 7
  norm_num at h2 h5 h7
  calc
    _ ≤ 5 * ((s : ℝ) / 9) + 2 * (17 / 32 : ℝ) *
          ((s : ℝ) * (5 / 12)) + (7 / 15 : ℝ) * ((s : ℝ) / 9) +
          (3 / 7 : ℝ) * ((s : ℝ) / 9) := by gcongr
    _ = (66391 / 60480 : ℝ) * s := by ring

/-! ## Selected prime two in the two degrees where the full order budget closes -/

theorem refinedBudget_twenty_traceyPrimary_two
    (s e : ℕ) (he : 5 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate s 2 e) 20 ≤
      (187 / 480 : ℝ) * s := by
  rw [refinedWeightedFactorBudget_twenty]
  have hpow : 32 ≤ 2 ^ e :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) he
  have h2 := traceyPrimaryRate_two_matching_of_five_le s e he
  have h5 := traceyPrimaryRate_nonmatching_le s 2 e 5 32 (by norm_num) hpow (by norm_num)
  have hslope5 := logb_two_five_div_five_lt_seven_fifteenths.le
  have hr5 := rate_nonneg s 2 e 5
  norm_num at h5
  calc
    _ ≤ (s : ℝ) * (3 / 8) + (7 / 15 : ℝ) * ((s : ℝ) / 32) := by gcongr
    _ = (187 / 480 : ℝ) * s := by ring

theorem refinedBudget_fourThirtyTwo_traceyPrimary_two
    (s e : ℕ) (he : 4 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate s 2 e) 432 ≤
      (1433 / 1536 : ℝ) * s := by
  rw [refinedWeightedFactorBudget_fourThirtyTwo]
  have hpow : 16 ≤ 2 ^ e :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) he
  have h2 := traceyPrimaryRate_two_matching_of_four_le s e he
  have h3 := traceyPrimaryRate_nonmatching_le s 2 e 3 16 (by norm_num) hpow (by norm_num)
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hr3 := rate_nonneg s 2 e 3
  norm_num at h3
  calc
    _ ≤ 2 * ((s : ℝ) * (5 / 12)) + 3 * (17 / 32 : ℝ) *
          ((s : ℝ) / 16) := by gcongr
    _ = (1433 / 1536 : ℝ) * s := by ring

/-! ## Common margin conversion -/

/-- Convert a retained budget `eta ≤ k s` into the exact affine-component
margin.  The `1/16` pays for the possible one-point parity loss, using the
fact that a genuine imprimitive block system has at least two blocks. -/
theorem smallAffine_budget_margin
    (r s w : ℕ) (hs : 2 ≤ s) (hw : w = r * s)
    (k eta : ℝ)
    (hnum : Non2UnipotentPrefixFiniteMenu.preE7CharacterRho * (r : ℝ) +
        k + 1 / 16 ≤ ((r : ℝ) - 1) / 8)
    (heta : eta ≤ k * s) :
    Non2UnipotentPrefixFiniteMenu.preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - s) / 8 - eta := by
  have heven : (w : ℝ) ≤ evenWidth w + 1 := by
    exact_mod_cast width_le_evenWidth_add_one w
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hwR : (w : ℝ) = r * s := by exact_mod_cast hw
  rw [hwR] at heven ⊢
  ring_nf at heven hnum heta ⊢
  nlinarith

end SymmetricSubgroupAsymptotics

end
