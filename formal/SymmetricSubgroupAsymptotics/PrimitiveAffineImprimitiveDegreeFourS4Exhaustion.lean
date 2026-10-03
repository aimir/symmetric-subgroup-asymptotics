import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveDegreeFourA4Exhaustion

/-!
# Degree-four affine components of order dividing twenty-four

This is the exact numerical `S4` half of the local degree-four capacity
table.  It accepts every block count outside the binary pair-frame counts
and `5,10,15,20,30,60`.  The isolated count eighteen is proved with the
integral retained capacity, so no rounded real estimate is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- If no prime at least seven occurs and the binary, ternary and
prime-five valuations are bounded, the integer divides the corresponding
`2,3,5` product. -/
theorem dvd_binary_ternary_five_bounded
    {s a b c : ℕ} (hs : s ≠ 0)
    (hlarge : ¬ ∃ q : ℕ, q.Prime ∧ q ∣ s ∧ 7 ≤ q)
    (h2 : ¬ 2 ^ (a + 1) ∣ s) (h3 : ¬ 3 ^ (b + 1) ∣ s)
    (h5 : ¬ 5 ^ (c + 1) ∣ s) :
    s ∣ 2 ^ a * 3 ^ b * 5 ^ c := by
  rw [← Nat.factorization_le_iff_dvd hs (by positivity)]
  intro p
  by_cases hp : p.Prime
  · by_cases hps : p ∣ s
    · have hp7 : p < 7 := by
        by_contra h
        exact hlarge ⟨p, hp, hps, by omega⟩
      have hp235 : p = 2 ∨ p = 3 ∨ p = 5 := by
        have hp2 := hp.two_le
        have hpne4 : p ≠ 4 := by
          intro hp4
          subst p
          norm_num at hp
        have hpne6 : p ≠ 6 := by
          intro hp6
          subst p
          norm_num at hp
        omega
      rcases hp235 with rfl | rfl | rfl
      · have hvnot : ¬ a + 1 ≤ s.factorization 2 := by
          intro hv
          exact h2 ((Nat.prime_two.pow_dvd_iff_le_factorization hs).mpr hv)
        have hv : s.factorization 2 ≤ a := by omega
        rw [Nat.factorization_mul
          (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
          (pow_ne_zero _ (by norm_num)),
          Nat.factorization_mul (pow_ne_zero _ (by norm_num))
            (pow_ne_zero _ (by norm_num)), Nat.factorization_pow,
          Nat.factorization_pow, Nat.factorization_pow]
        change s.factorization 2 ≤
          (a * (Nat.factorization 2) 2 + b * (Nat.factorization 3) 2) +
            c * (Nat.factorization 5) 2
        rw [Nat.Prime.factorization_self Nat.prime_two,
          Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3),
          Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 5)]
        simpa using hv
      · have hvnot : ¬ b + 1 ≤ s.factorization 3 := by
          intro hv
          exact h3 (((by norm_num : Nat.Prime 3).pow_dvd_iff_le_factorization hs).mpr hv)
        have hv : s.factorization 3 ≤ b := by omega
        rw [Nat.factorization_mul
          (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
          (pow_ne_zero _ (by norm_num)),
          Nat.factorization_mul (pow_ne_zero _ (by norm_num))
            (pow_ne_zero _ (by norm_num)), Nat.factorization_pow,
          Nat.factorization_pow, Nat.factorization_pow]
        change s.factorization 3 ≤
          (a * (Nat.factorization 2) 3 + b * (Nat.factorization 3) 3) +
            c * (Nat.factorization 5) 3
        rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2),
          Nat.Prime.factorization_self (by norm_num : Nat.Prime 3),
          Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 5)]
        simpa using hv
      · have hvnot : ¬ c + 1 ≤ s.factorization 5 := by
          intro hv
          exact h5 (((by norm_num : Nat.Prime 5).pow_dvd_iff_le_factorization hs).mpr hv)
        have hv : s.factorization 5 ≤ c := by omega
        rw [Nat.factorization_mul
          (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
          (pow_ne_zero _ (by norm_num)),
          Nat.factorization_mul (pow_ne_zero _ (by norm_num))
            (pow_ne_zero _ (by norm_num)), Nat.factorization_pow,
          Nat.factorization_pow, Nat.factorization_pow]
        change s.factorization 5 ≤
          (a * (Nat.factorization 2) 5 + b * (Nat.factorization 3) 5) +
            c * (Nat.factorization 5) 5
        rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 2),
          Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 3),
          Nat.Prime.factorization_self (by norm_num : Nat.Prime 5)]
        simpa using hv
    · rw [Nat.factorization_eq_zero_of_not_dvd hps]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

/-- The middle coefficient in the ternary soluble prime-power rate has
density at most `3/8` from exponent two onward. -/
theorem ternary_middle_le_three_eighths (e : ℕ) (he : 2 ≤ e) :
    8 * (2 * e).choose e ≤ 3 * 2 ^ (2 * e) := by
  by_cases he2 : e = 2
  · subst e
    decide
  · have hfive : 5 ≤ 2 * e := by omega
    have h := binary_middle_le_five_sixteenths (2 * e) hfive
    rw [Nat.mul_div_cancel_left e (by norm_num : 0 < 2)] at h
    have hp : 0 < 2 ^ (2 * e) := pow_pos (by norm_num) _
    omega

theorem integralRefinedWeightedFactorBudget_twentyFour (rate : ℕ → ℝ) :
    integralRefinedWeightedFactorBudget rate 24 =
      (1 / 2 : ℝ) * (Nat.floor (3 * rate 2) : ℝ) +
        fixedTargetCompositionGamma * (Nat.floor (rate 3) : ℝ) := by
  rw [show 24 = 2 ^ 3 * 3 ^ 1 by norm_num,
    integralRefinedWeightedFactorBudget_mul_of_coprime rate (by decide),
    integralRefinedWeightedFactorBudget_prime_pow rate Nat.prime_two,
    integralRefinedWeightedFactorBudget_prime_pow rate
      (by norm_num : Nat.Prime 3)]
  unfold fixedTargetCompositionGamma
  norm_num [Real.logb_self_eq_one]

namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace ComponentSource

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
  (hTraceyLog : TraceyAffineInducedModuleInput)
  (hTraceyRefined : TraceyRefinedInducedModuleInput)
  (hTraceyPerm : TraceyPermutationGeneratorInput)
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)

private abbrev blocks := Nat.card block.Points

private theorem blocks_ne_zero : blocks block ≠ 0 :=
  (Nat.card_pos (α := block.Points)).ne'

private theorem valuation_ge_of_pow_dvd
    {q d : ℕ} (hq : q.Prime) (hpow : q ^ d ∣ blocks block) :
    d ≤ (blocks block).factorization q := by
  exact (hq.pow_dvd_iff_le_factorization (blocks_ne_zero block)).mp hpow

private theorem width_even (hr : Nat.card block.Fibre = 4) : Even w := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  rw [width_eq block, hr]
  exact ⟨2 * Nat.card block.Points, by ring⟩

private def degreeFourS4MixedRate (s q₁ e₁ q₂ e₂ p : ℕ) : ℝ :=
  min (ActualWreathCompressionTower.traceyPrimaryRate s q₁ e₁ p)
    (ActualWreathCompressionTower.traceyPrimaryRate s q₂ e₂ p)

private theorem budget_twentyFour_largePrime
    (q e : ℕ) (hq7 : 7 ≤ q) (he : 1 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate (blocks block) q e) 24 ≤
      (65 / 224 : ℝ) * blocks block := by
  rw [refinedWeightedFactorBudget_twentyFour]
  have h2 := traceyPrimaryRate_nonmatching_le (blocks block) q e 2 7
    (by omega) (by
      calc 7 ≤ q := hq7
        _ = q ^ 1 := by simp
        _ ≤ q ^ e := Nat.pow_le_pow_right (by omega) he) (by norm_num)
  have h3 := traceyPrimaryRate_nonmatching_le (blocks block) q e 3 7
    (by omega) (by
      calc 7 ≤ q := hq7
        _ = q ^ 1 := by simp
        _ ≤ q ^ e := Nat.pow_le_pow_right (by omega) he) (by norm_num)
  have h2' : ActualWreathCompressionTower.traceyPrimaryRate
      (blocks block) q e 2 ≤ (blocks block : ℝ) / 7 := by
    simpa only [blocks] using h2
  have h3' : ActualWreathCompressionTower.traceyPrimaryRate
      (blocks block) q e 3 ≤ (blocks block : ℝ) / 7 := by
    simpa only [blocks] using h3
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hr3 := ActualWreathCompressionTower.traceyPrimaryRate_nonneg
    (blocks block) q e 3
  calc
    _ ≤ (3 / 2 : ℝ) * ((blocks block : ℝ) / 7) +
        (17 / 32 : ℝ) * ((blocks block : ℝ) / 7) := by gcongr
    _ = (65 / 224 : ℝ) * blocks block := by ring

noncomputable def of_degreeFour_twentyFour_largePrime
    (hr : Nat.card block.Fibre = 4)
    (hcomponent : Nat.card block.Component ∣ 24)
    (q e : ℕ) (hq : q.Prime) (hq7 : 7 ≤ q)
    (he : 1 ≤ e) (hdiv : q ^ e ∣ blocks block)
    (hmax : ¬ q ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P q e 24 hq he hdiv hmax (by norm_num) hcomponent
  apply smallAffine_even_budget_margin 4 (blocks block) w
      (by simpa only [hr] using width_eq block) (width_even block hr)
      (65 / 224) _
  · unfold preE7CharacterRho
    norm_num
  · exact budget_twentyFour_largePrime block q e hq7 he

private theorem budget_twentyFour_fiveTwo
    (e : ℕ) (he : 2 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate (blocks block) 5 e) 24 ≤
      (13 / 160 : ℝ) * blocks block := by
  rw [refinedWeightedFactorBudget_twentyFour]
  have hpow : 25 ≤ 5 ^ e := Nat.pow_le_pow_right (by norm_num : 0 < 5) he
  have h2 := traceyPrimaryRate_nonmatching_le (blocks block) 5 e 2 25
    (by norm_num) hpow (by norm_num)
  have h3 := traceyPrimaryRate_nonmatching_le (blocks block) 5 e 3 25
    (by norm_num) hpow (by norm_num)
  have h2' : ActualWreathCompressionTower.traceyPrimaryRate
      (blocks block) 5 e 2 ≤ (blocks block : ℝ) / 25 := by
    simpa only [blocks] using h2
  have h3' : ActualWreathCompressionTower.traceyPrimaryRate
      (blocks block) 5 e 3 ≤ (blocks block : ℝ) / 25 := by
    simpa only [blocks] using h3
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hr3 := ActualWreathCompressionTower.traceyPrimaryRate_nonneg
    (blocks block) 5 e 3
  calc
    _ ≤ (3 / 2 : ℝ) * ((blocks block : ℝ) / 25) +
        (17 / 32 : ℝ) * ((blocks block : ℝ) / 25) := by gcongr
    _ = (13 / 160 : ℝ) * blocks block := by ring

noncomputable def of_degreeFour_twentyFour_fiveTwo
    (hr : Nat.card block.Fibre = 4)
    (hcomponent : Nat.card block.Component ∣ 24)
    (e : ℕ) (he : 2 ≤ e) (hdiv : 5 ^ e ∣ blocks block)
    (hmax : ¬ 5 ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P 5 e 24 (by norm_num) (by omega) hdiv hmax (by norm_num) hcomponent
  apply smallAffine_even_budget_margin 4 (blocks block) w
      (by simpa only [hr] using width_eq block) (width_even block hr)
      (13 / 160) _
  · unfold preE7CharacterRho
    norm_num
  · exact budget_twentyFour_fiveTwo block e he

private theorem budget_twentyFour_fiveEight
    (e₅ e₂ : ℕ) (he₅ : 1 ≤ e₅) (he₂ : 3 ≤ e₂) :
    refinedWeightedFactorBudget
        (degreeFourS4MixedRate (blocks block) 5 e₅ 2 e₂) 24 ≤
      (469 / 1280 : ℝ) * blocks block := by
  rw [refinedWeightedFactorBudget_twentyFour]
  have h2 : degreeFourS4MixedRate (blocks block) 5 e₅ 2 e₂ 2 ≤
      (blocks block : ℝ) / 5 :=
    (min_le_left _ _).trans
      (traceyPrimaryRate_nonmatching_le (blocks block) 5 e₅ 2 5
        (by norm_num) (Nat.pow_le_pow_right (by norm_num : 0 < 5) he₅)
        (by norm_num))
  have h3 : degreeFourS4MixedRate (blocks block) 5 e₅ 2 e₂ 3 ≤
      (blocks block : ℝ) / 8 :=
    (min_le_right _ _).trans
      (traceyPrimaryRate_nonmatching_le (blocks block) 2 e₂ 3 8
        (by norm_num) (Nat.pow_le_pow_right (by norm_num : 0 < 2) he₂)
        (by norm_num))
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hr3 : 0 ≤ degreeFourS4MixedRate (blocks block) 5 e₅ 2 e₂ 3 := le_min
    (ActualWreathCompressionTower.traceyPrimaryRate_nonneg _ _ _ _)
    (ActualWreathCompressionTower.traceyPrimaryRate_nonneg _ _ _ _)
  calc
    _ ≤ (3 / 2 : ℝ) * ((blocks block : ℝ) / 5) +
        (17 / 32 : ℝ) * ((blocks block : ℝ) / 8) := by gcongr
    _ = (469 / 1280 : ℝ) * blocks block := by ring

private theorem budget_twentyFour_fiveNine
    (e₅ e₃ : ℕ) (he₅ : 1 ≤ e₅) (he₃ : 2 ≤ e₃) :
    refinedWeightedFactorBudget
        (degreeFourS4MixedRate (blocks block) 5 e₅ 3 e₃) 24 ≤
      (131 / 480 : ℝ) * blocks block := by
  rw [refinedWeightedFactorBudget_twentyFour]
  have h2 : degreeFourS4MixedRate (blocks block) 5 e₅ 3 e₃ 2 ≤
      (blocks block : ℝ) / 9 :=
    (min_le_right _ _).trans
      (traceyPrimaryRate_nonmatching_le (blocks block) 3 e₃ 2 9
        (by norm_num) (Nat.pow_le_pow_right (by norm_num : 0 < 3) he₃)
        (by norm_num))
  have h3 : degreeFourS4MixedRate (blocks block) 5 e₅ 3 e₃ 3 ≤
      (blocks block : ℝ) / 5 :=
    (min_le_left _ _).trans
      (traceyPrimaryRate_nonmatching_le (blocks block) 5 e₅ 3 5
        (by norm_num) (Nat.pow_le_pow_right (by norm_num : 0 < 5) he₅)
        (by norm_num))
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hr3 : 0 ≤ degreeFourS4MixedRate (blocks block) 5 e₅ 3 e₃ 3 := le_min
    (ActualWreathCompressionTower.traceyPrimaryRate_nonneg _ _ _ _)
    (ActualWreathCompressionTower.traceyPrimaryRate_nonneg _ _ _ _)
  calc
    _ ≤ (3 / 2 : ℝ) * ((blocks block : ℝ) / 9) +
        (17 / 32 : ℝ) * ((blocks block : ℝ) / 5) := by gcongr
    _ = (131 / 480 : ℝ) * blocks block := by ring

noncomputable def of_degreeFour_twentyFour_twoPrimary
    (hr : Nat.card block.Fibre = 4)
    (hcomponent : Nat.card block.Component ∣ 24)
    (q₁ e₁ q₂ e₂ : ℕ)
    (hq₁ : q₁.Prime) (he₁ : 1 ≤ e₁)
    (hdiv₁ : q₁ ^ e₁ ∣ blocks block) (hmax₁ : ¬ q₁ ^ (e₁ + 1) ∣ blocks block)
    (hq₂ : q₂.Prime) (he₂ : 1 ≤ e₂)
    (hdiv₂ : q₂ ^ e₂ ∣ blocks block) (hmax₂ : ¬ q₂ ^ (e₂ + 1) ∣ blocks block)
    (k : ℝ)
    (hbudget : refinedWeightedFactorBudget
      (degreeFourS4MixedRate (blocks block) q₁ e₁ q₂ e₂) 24 ≤
        k * blocks block)
    (hnum : preE7CharacterRho * (4 : ℝ) + k ≤ (3 : ℝ) / 8) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_twoTraceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P q₁ e₁ q₂ e₂ 24 hq₁ he₁ hdiv₁ hmax₁ hq₂ he₂
      hdiv₂ hmax₂ (by norm_num) hcomponent
  apply smallAffine_even_budget_margin 4 (blocks block) w
      (by simpa only [hr] using width_eq block) (width_even block hr) k _
      (by
        convert hnum using 1
        all_goals norm_num)
  simpa only [degreeFourS4MixedRate] using hbudget

private theorem primePowerRate_two_nine_s4
    (e : ℕ) (he : 9 ≤ e) :
    ActualWreathCompressionTower.traceyPrimePowerRate 2 e 2 ≤
      (63 / 256 : ℝ) * (2 ^ e : ℕ) := by
  unfold ActualWreathCompressionTower.traceyPrimePowerRate
  rw [if_pos rfl]
  simp only [Nat.reduceSubDiff, Nat.mul_one]
  have hmiddle : (256 : ℝ) * (e.choose (e / 2) : ℝ) ≤
      63 * (2 : ℝ) ^ e := by
    exact_mod_cast binary_middle_le_sixtyThree_twoFiftySix e he
  have hp : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  norm_num [Nat.cast_pow] at hmiddle ⊢
  field_simp
  nlinarith

private theorem budget_twentyFour_binaryPrimePowerNine
    (e : ℕ) (he : 9 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimePowerRate 2 e) 24 ≤
      (6065 / 16384 : ℝ) * (2 ^ e : ℕ) := by
  rw [refinedWeightedFactorBudget_twentyFour]
  have h2 := primePowerRate_two_nine_s4 e he
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hs512 : (512 : ℝ) ≤ (2 ^ e : ℕ) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) he
  have h3 : ActualWreathCompressionTower.traceyPrimePowerRate 2 e 3 = 1 := by
    simp [ActualWreathCompressionTower.traceyPrimePowerRate]
  rw [h3]
  simp only [mul_one]
  calc
    _ ≤ (3 / 2 : ℝ) * ((63 / 256 : ℝ) * (2 ^ e : ℕ)) +
        17 / 32 := by gcongr
    _ ≤ (6065 / 16384 : ℝ) * (2 ^ e : ℕ) := by nlinarith

noncomputable def of_degreeFour_twentyFour_binaryPrimePowerNine
    (hr : Nat.card block.Fibre = 4)
    (hcomponent : Nat.card block.Component ∣ 24)
    (e : ℕ) (he : 9 ≤ e) (hs : blocks block = 2 ^ e) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimePower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P 2 e 24 Nat.prime_two (by omega) hs (by norm_num) hcomponent
  apply smallAffine_even_budget_margin 4 (blocks block) w
      (by simpa only [hr] using width_eq block) (width_even block hr)
      (6065 / 16384) _
  · unfold preE7CharacterRho
    norm_num
  · rw [hs]
    exact budget_twentyFour_binaryPrimePowerNine e he

private theorem primePowerRate_three_two
    (e : ℕ) (he : 2 ≤ e) :
    ActualWreathCompressionTower.traceyPrimePowerRate 3 e 3 ≤
      (3 / 8 : ℝ) * (3 ^ e : ℕ) := by
  unfold ActualWreathCompressionTower.traceyPrimePowerRate
  rw [if_pos rfl]
  have hmiddle : (8 : ℝ) * ((2 * e).choose e : ℝ) ≤
      3 * (2 : ℝ) ^ (2 * e) := by
    exact_mod_cast ternary_middle_le_three_eighths e he
  have hp : (0 : ℝ) < (2 : ℝ) ^ (2 * e) := by positivity
  norm_num [Nat.cast_pow] at hmiddle ⊢
  have hratio : ((2 * e).choose e : ℝ) / (2 : ℝ) ^ (2 * e) ≤ 3 / 8 := by
    apply (div_le_iff₀ hp).2
    nlinarith
  rw [show e * 2 = 2 * e by omega]
  calc
    (3 : ℝ) ^ e * ((2 * e).choose e : ℝ) / (2 : ℝ) ^ (2 * e) =
        (3 : ℝ) ^ e *
          (((2 * e).choose e : ℝ) / (2 : ℝ) ^ (2 * e)) := by ring
    _ ≤ (3 : ℝ) ^ e * (3 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = (3 / 8 : ℝ) * (3 : ℝ) ^ e := by ring

private theorem budget_twentyFour_ternaryPrimePowerTwo
    (e : ℕ) (he : 2 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimePowerRate 3 e) 24 ≤
      (281 / 768 : ℝ) * (3 ^ e : ℕ) := by
  rw [refinedWeightedFactorBudget_twentyFour]
  have h3 := primePowerRate_three_two e he
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hs9 : (9 : ℝ) ≤ (3 ^ e : ℕ) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 3) he
  have h2 : ActualWreathCompressionTower.traceyPrimePowerRate 3 e 2 = 1 := by
    simp [ActualWreathCompressionTower.traceyPrimePowerRate]
  rw [h2]
  have hr3 : 0 ≤ ActualWreathCompressionTower.traceyPrimePowerRate 3 e 3 :=
    ActualWreathCompressionTower.traceyPrimePowerRate_nonneg 3 e 3
  calc
    _ = (3 / 2 : ℝ) + fixedTargetCompositionGamma *
        ActualWreathCompressionTower.traceyPrimePowerRate 3 e 3 := by ring
    _ ≤ (3 / 2 : ℝ) + (17 / 32 : ℝ) *
        ((3 / 8 : ℝ) * (3 ^ e : ℕ)) := by gcongr
    _ ≤ (281 / 768 : ℝ) * (3 ^ e : ℕ) := by nlinarith

noncomputable def of_degreeFour_twentyFour_ternaryPrimePowerTwo
    (hr : Nat.card block.Fibre = 4)
    (hcomponent : Nat.card block.Component ∣ 24)
    (e : ℕ) (he : 2 ≤ e) (hs : blocks block = 3 ^ e) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimePower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P 3 e 24 (by norm_num) (by omega) hs (by norm_num) hcomponent
  apply smallAffine_even_budget_margin 4 (blocks block) w
      (by simpa only [hr] using width_eq block) (width_even block hr)
      (281 / 768) _
  · unfold preE7CharacterRho
    norm_num
  · rw [hs]
    exact budget_twentyFour_ternaryPrimePowerTwo e he

private theorem budget_twentyFour_mixed_fourNine
    (e₂ e₃ : ℕ) (he₂ : 2 ≤ e₂) (he₃ : 2 ≤ e₃) :
    refinedWeightedFactorBudget
        (degreeFourS4MixedRate (blocks block) 2 e₂ 3 e₃) 24 ≤
      (115 / 384 : ℝ) * blocks block := by
  rw [refinedWeightedFactorBudget_twentyFour]
  have h2 : degreeFourS4MixedRate (blocks block) 2 e₂ 3 e₃ 2 ≤
      (blocks block : ℝ) / 9 :=
    (min_le_right _ _).trans
      (traceyPrimaryRate_nonmatching_le (blocks block) 3 e₃ 2 9
        (by norm_num) (Nat.pow_le_pow_right (by norm_num : 0 < 3) he₃)
        (by norm_num))
  have h3 : degreeFourS4MixedRate (blocks block) 2 e₂ 3 e₃ 3 ≤
      (blocks block : ℝ) / 4 :=
    (min_le_left _ _).trans
      (traceyPrimaryRate_nonmatching_le (blocks block) 2 e₂ 3 4
        (by norm_num) (Nat.pow_le_pow_right (by norm_num : 0 < 2) he₂)
        (by norm_num))
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hr3 : 0 ≤ degreeFourS4MixedRate (blocks block) 2 e₂ 3 e₃ 3 := le_min
    (ActualWreathCompressionTower.traceyPrimaryRate_nonneg _ _ _ _)
    (ActualWreathCompressionTower.traceyPrimaryRate_nonneg _ _ _ _)
  calc
    _ ≤ (3 / 2 : ℝ) * ((blocks block : ℝ) / 9) +
        (17 / 32 : ℝ) * ((blocks block : ℝ) / 4) := by gcongr
    _ = (115 / 384 : ℝ) * blocks block := by ring

private theorem budget_twentyFour_mixed_twoTwentySeven
    (e₂ e₃ : ℕ) (he₂ : 1 ≤ e₂) (he₃ : 3 ≤ e₃) :
    refinedWeightedFactorBudget
        (degreeFourS4MixedRate (blocks block) 2 e₂ 3 e₃) 24 ≤
      (185 / 576 : ℝ) * blocks block := by
  rw [refinedWeightedFactorBudget_twentyFour]
  have h2 : degreeFourS4MixedRate (blocks block) 2 e₂ 3 e₃ 2 ≤
      (blocks block : ℝ) / 27 :=
    (min_le_right _ _).trans
      (traceyPrimaryRate_nonmatching_le (blocks block) 3 e₃ 2 27
        (by norm_num) (Nat.pow_le_pow_right (by norm_num : 0 < 3) he₃)
        (by norm_num))
  have h3 : degreeFourS4MixedRate (blocks block) 2 e₂ 3 e₃ 3 ≤
      (blocks block : ℝ) / 2 :=
    (min_le_left _ _).trans
      (traceyPrimaryRate_nonmatching_le (blocks block) 2 e₂ 3 2
        (by norm_num) (Nat.pow_le_pow_right (by norm_num : 0 < 2) he₂)
        (by norm_num))
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hr3 : 0 ≤ degreeFourS4MixedRate (blocks block) 2 e₂ 3 e₃ 3 := le_min
    (ActualWreathCompressionTower.traceyPrimaryRate_nonneg _ _ _ _)
    (ActualWreathCompressionTower.traceyPrimaryRate_nonneg _ _ _ _)
  calc
    _ ≤ (3 / 2 : ℝ) * ((blocks block : ℝ) / 27) +
        (17 / 32 : ℝ) * ((blocks block : ℝ) / 2) := by gcongr
    _ = (185 / 576 : ℝ) * blocks block := by ring

private theorem sqrt_two_over_three_e_le_seventyNine_threeTwenty
    (e : ℕ) (he : 11 ≤ e) :
    Real.sqrt (2 / (3 * (e : ℝ))) ≤ (79 : ℝ) / 320 := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num
  · have hden : (33 : ℝ) ≤ 3 * e := by
      exact_mod_cast (Nat.mul_le_mul_left 3 he)
    have hfrac : (2 : ℝ) / (3 * e) ≤ 2 / 33 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
    norm_num at hfrac ⊢
    nlinarith

private theorem budget_twentyFour_binaryEleven
    (e : ℕ) (he : 11 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate (blocks block) 2 e) 24 ≤
      ((237 / 640 : ℝ) + 17 / 65536) * blocks block := by
  rw [refinedWeightedFactorBudget_twentyFour]
  have h2 : ActualWreathCompressionTower.traceyPrimaryRate
      (blocks block) 2 e 2 ≤ (blocks block : ℝ) * (79 / 320 : ℝ) := by
    apply traceyPrimaryRate_matching_le
    convert sqrt_two_over_three_e_le_seventyNine_threeTwenty e he using 1
    all_goals norm_num
  have hpow : 2048 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num : 0 < 2) he
  have h3 := traceyPrimaryRate_nonmatching_le (blocks block) 2 e 3 2048
    (by norm_num) hpow (by norm_num)
  have h3' : ActualWreathCompressionTower.traceyPrimaryRate
      (blocks block) 2 e 3 ≤ (blocks block : ℝ) / 2048 := by
    simpa only [blocks] using h3
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hr3 := ActualWreathCompressionTower.traceyPrimaryRate_nonneg
    (blocks block) 2 e 3
  calc
    _ ≤ (3 / 2 : ℝ) * ((blocks block : ℝ) * (79 / 320)) +
        (17 / 32 : ℝ) * ((blocks block : ℝ) / 2048) := by gcongr
    _ = ((237 / 640 : ℝ) + 17 / 65536) * blocks block := by ring

noncomputable def of_degreeFour_twentyFour_binaryEleven
    (hr : Nat.card block.Fibre = 4)
    (hcomponent : Nat.card block.Component ∣ 24)
    (e : ℕ) (he : 11 ≤ e) (hdiv : 2 ^ e ∣ blocks block)
    (hmax : ¬ 2 ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P 2 e 24 Nat.prime_two (by omega) hdiv hmax (by norm_num) hcomponent
  apply smallAffine_even_budget_margin 4 (blocks block) w
      (by simpa only [hr] using width_eq block) (width_even block hr)
      ((237 / 640 : ℝ) + 17 / 65536) _
  · unfold preE7CharacterRho
    norm_num
  · exact budget_twentyFour_binaryEleven block e he

private def rateEighteen (p : ℕ) : ℝ :=
  degreeFourS4MixedRate 18 2 1 3 2 p

private theorem integralBudget_eighteen :
    integralRefinedWeightedFactorBudget rateEighteen 24 ≤ (215 / 32 : ℝ) := by
  rw [integralRefinedWeightedFactorBudget_twentyFour]
  have h2 : rateEighteen 2 ≤ 2 := by
    exact (min_le_right _ _).trans (by
      have h := traceyPrimaryRate_nonmatching_le 18 3 2 2 9
        (by norm_num) (by norm_num) (by norm_num)
      norm_num at h ⊢
      exact h)
  have h3 : rateEighteen 3 ≤ 15 / 2 := by
    exact (min_le_right _ _).trans (by
      have h := traceyPrimaryRate_three_matching_of_two_le 18 2 (by norm_num)
      norm_num at h ⊢
      exact h)
  have hfloor2 : Nat.floor (3 * rateEighteen 2) ≤ 6 := by
    have hm := Nat.floor_mono (show 3 * rateEighteen 2 ≤ (6 : ℝ) by nlinarith)
    norm_num at hm ⊢
    exact hm
  have hfloor3 : Nat.floor (rateEighteen 3) ≤ 7 := by
    have hlt : rateEighteen 3 < (8 : ℝ) := by linarith
    exact Nat.lt_succ_iff.mp ((Nat.floor_lt (by
      exact le_min
        (ActualWreathCompressionTower.traceyPrimaryRate_nonneg 18 2 1 3)
        (ActualWreathCompressionTower.traceyPrimaryRate_nonneg 18 3 2 3))).mpr hlt)
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hgamma0 : 0 ≤ fixedTargetCompositionGamma := by
    unfold fixedTargetCompositionGamma
    exact div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)
  have hfloor2R : (Nat.floor (3 * rateEighteen 2) : ℝ) ≤ 6 := by
    exact_mod_cast hfloor2
  have hfloor3R : (Nat.floor (rateEighteen 3) : ℝ) ≤ 7 := by
    exact_mod_cast hfloor3
  calc
    _ ≤ (1 / 2 : ℝ) * 6 + fixedTargetCompositionGamma * 7 := by gcongr
    _ ≤ (1 / 2 : ℝ) * 6 + (17 / 32 : ℝ) * 7 := by gcongr
    _ = (215 / 32 : ℝ) := by norm_num

noncomputable def of_integralTwoTraceyPrimary
    (q₁ e₁ q₂ e₂ n : ℕ)
    (hq₁ : q₁.Prime) (he₁ : 1 ≤ e₁)
    (hdiv₁ : q₁ ^ e₁ ∣ blocks block) (hmax₁ : ¬ q₁ ^ (e₁ + 1) ∣ blocks block)
    (hq₂ : q₂.Prime) (he₂ : 1 ≤ e₂)
    (hdiv₂ : q₂ ^ e₂ ∣ blocks block) (hmax₂ : ¬ q₂ ^ (e₂ + 1) ∣ blocks block)
    (hn : n ≠ 0) (hcomponent : Nat.card block.Component ∣ n)
    (hmargin : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - Nat.card block.Points) / 8 -
        integralRefinedWeightedFactorBudget
          (degreeFourS4MixedRate (blocks block) q₁ e₁ q₂ e₂) n) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  apply of_integralRefinedFactorBudget hTraceyHalf hTraceyLog hTraceyRefined
    hTraceyPerm block P _
      (fun p => le_min
        (ActualWreathCompressionTower.traceyPrimaryRate_nonneg
          (blocks block) q₁ e₁ p)
        (ActualWreathCompressionTower.traceyPrimaryRate_nonneg
          (blocks block) q₂ e₂ p))
      n hn hcomponent
  · let T := tower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    apply ActualWreathCompressionTower.capacityRateBound_min _ _ T
    · simpa only [Fintype.card_eq_nat_card] using
        (ActualWreathCompressionTower.capacityRateBound_traceyPrimary
          q₁ e₁ hq₁ he₁
          (by simpa only [Fintype.card_eq_nat_card] using hdiv₁)
          (by simpa only [Fintype.card_eq_nat_card] using hmax₁) T)
    · simpa only [Fintype.card_eq_nat_card] using
        (ActualWreathCompressionTower.capacityRateBound_traceyPrimary
          q₂ e₂ hq₂ he₂
          (by simpa only [Fintype.card_eq_nat_card] using hdiv₂)
          (by simpa only [Fintype.card_eq_nat_card] using hmax₂) T)
  · simpa only [degreeFourS4MixedRate] using hmargin

noncomputable def of_degreeFour_twentyFour_eighteen
    (hr : Nat.card block.Fibre = 4)
    (hcomponent : Nat.card block.Component ∣ 24)
    (hs : blocks block = 18) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_integralTwoTraceyPrimary hTraceyHalf hTraceyLog hTraceyRefined
    hTraceyPerm block P 2 1 3 2 24 Nat.prime_two (by norm_num)
      (by rw [hs]; norm_num) (by rw [hs]; norm_num)
      (by norm_num) (by norm_num) (by rw [hs]; norm_num)
      (by rw [hs]; norm_num) (by norm_num) hcomponent
  have hw : w = 72 := by simpa only [hr, hs] using width_eq block
  have hbudget : integralRefinedWeightedFactorBudget
      (degreeFourS4MixedRate (blocks block) 2 1 3 2) 24 ≤ 215 / 32 := by
    simpa only [hs, rateEighteen] using integralBudget_eighteen
  calc
    preE7CharacterRho * w = (1 / 8192 : ℝ) * 72 := by rw [hw]; rfl
    _ ≤ ((72 : ℝ) - 18) / 8 - 215 / 32 := by norm_num
    _ ≤ ((evenWidth w : ℝ) - Nat.card block.Points) / 8 -
        integralRefinedWeightedFactorBudget
          (degreeFourS4MixedRate (blocks block) 2 1 3 2) 24 := by
      have hew : evenWidth w = 72 := by simp [hw, evenWidth, halfDegree]
      have hs' : Nat.card block.Points = 18 := by simpa only [blocks] using hs
      rw [hew, hs']
      linarith

/-- The exact order-twenty-four exception set. -/
def IsDegreeFourTwentyFourExceptionalBlockCount (s : ℕ) : Prop :=
  IsDegreeTwoAffineExceptionalBlockCount s ∨
    s = 5 ∨ s = 10 ∨ s = 15 ∨ s = 20 ∨ s = 30 ∨ s = 60

/-- Degree four/order twenty-four: every block count is accepted outside
the exact `S4` exception set. -/
noncomputable def degreeFourTwentyFourExhaustion
    (hr : Nat.card block.Fibre = 4)
    (hcomponent : Nat.card block.Component ∣ 24) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P ⊕
      PLift (IsDegreeFourTwentyFourExceptionalBlockCount (blocks block)) := by
  by_cases hlarge : ∃ q : ℕ, q.Prime ∧ q ∣ blocks block ∧ 7 ≤ q
  · let q := Classical.choose hlarge
    have hqdata := Classical.choose_spec hlarge
    let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      hqdata.1 hqdata.2.1
    exact .inl (of_degreeFour_twentyFour_largePrime hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm block P hr hcomponent q E.e hqdata.1
        hqdata.2.2 E.one_le E.pow_dvd E.pow_succ_not_dvd)
  by_cases h25 : 5 ^ 2 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      (by norm_num : Nat.Prime 5) (dvd_trans (by norm_num : 5 ∣ 5 ^ 2) h25)
    have he : 2 ≤ E.e := by
      simpa only [E, ExactPrimaryDivisor.ofPrimeDvd] using
        (valuation_ge_of_pow_dvd block (by norm_num : Nat.Prime 5) h25)
    exact .inl (of_degreeFour_twentyFour_fiveTwo hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm block P hr hcomponent E.e he E.pow_dvd
        E.pow_succ_not_dvd)
  by_cases h5 : 5 ∣ blocks block
  · by_cases h8 : 2 ^ 3 ∣ blocks block
    · let E₂ := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
        Nat.prime_two (dvd_trans (by norm_num : 2 ∣ 2 ^ 3) h8)
      let E₅ := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
        (by norm_num : Nat.Prime 5) h5
      have he₂ : 3 ≤ E₂.e := by
        simpa only [E₂, ExactPrimaryDivisor.ofPrimeDvd] using
          (valuation_ge_of_pow_dvd block Nat.prime_two h8)
      exact .inl (of_degreeFour_twentyFour_twoPrimary hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P hr hcomponent 5 E₅.e 2 E₂.e
          (by norm_num) E₅.one_le E₅.pow_dvd E₅.pow_succ_not_dvd
          Nat.prime_two E₂.one_le E₂.pow_dvd E₂.pow_succ_not_dvd
          (469 / 1280) (budget_twentyFour_fiveEight block E₅.e E₂.e
            E₅.one_le he₂) (by unfold preE7CharacterRho; norm_num))
    · by_cases h9 : 3 ^ 2 ∣ blocks block
      · let E₃ := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
          (by norm_num : Nat.Prime 3) (dvd_trans (by norm_num : 3 ∣ 3 ^ 2) h9)
        let E₅ := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
          (by norm_num : Nat.Prime 5) h5
        have he₃ : 2 ≤ E₃.e := by
          simpa only [E₃, ExactPrimaryDivisor.ofPrimeDvd] using
            (valuation_ge_of_pow_dvd block (by norm_num : Nat.Prime 3) h9)
        exact .inl (of_degreeFour_twentyFour_twoPrimary hTraceyHalf hTraceyLog
          hTraceyRefined hTraceyPerm block P hr hcomponent 5 E₅.e 3 E₃.e
            (by norm_num) E₅.one_le E₅.pow_dvd E₅.pow_succ_not_dvd
            (by norm_num) E₃.one_le E₃.pow_dvd E₃.pow_succ_not_dvd
            (131 / 480) (budget_twentyFour_fiveNine block E₅.e E₃.e
              E₅.one_le he₃) (by unfold preE7CharacterRho; norm_num))
      · have hdvd : blocks block ∣ 2 ^ 2 * 3 ^ 1 * 5 ^ 1 :=
          dvd_binary_ternary_five_bounded (blocks_ne_zero block) hlarge h8 h9 h25
        have hs2 : 2 ≤ blocks block := block.degrees_ge_two.2
        have hs60 : blocks block ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd
        interval_cases hs : blocks block
        all_goals norm_num at hdvd
        all_goals norm_num at h5
        all_goals exact .inr ⟨by simp [IsDegreeFourTwentyFourExceptionalBlockCount]⟩
  · have hlarge5 : ¬ ∃ q : ℕ, q.Prime ∧ q ∣ blocks block ∧ 5 ≤ q := by
      rintro ⟨q, hq, hqdiv, hq5⟩
      by_cases hqeq : q = 5
      · exact h5 (by simpa [hqeq] using hqdiv)
      · have hqne6 : q ≠ 6 := by
          intro hq6
          subst q
          norm_num at hq
        exact hlarge ⟨q, hq, hqdiv, by omega⟩
    by_cases h3 : 3 ∣ blocks block
    · by_cases h9 : 3 ^ 2 ∣ blocks block
      · by_cases h2 : 2 ∣ blocks block
        · by_cases h4 : 2 ^ 2 ∣ blocks block
          · let E₂ := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
              Nat.prime_two h2
            let E₃ := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
              (by norm_num : Nat.Prime 3) h3
            have he₂ : 2 ≤ E₂.e := by
              simpa only [E₂, ExactPrimaryDivisor.ofPrimeDvd] using
                (valuation_ge_of_pow_dvd block Nat.prime_two h4)
            have he₃ : 2 ≤ E₃.e := by
              simpa only [E₃, ExactPrimaryDivisor.ofPrimeDvd] using
                (valuation_ge_of_pow_dvd block (by norm_num : Nat.Prime 3) h9)
            exact .inl (of_degreeFour_twentyFour_twoPrimary hTraceyHalf hTraceyLog
              hTraceyRefined hTraceyPerm block P hr hcomponent 2 E₂.e 3 E₃.e
                Nat.prime_two E₂.one_le E₂.pow_dvd E₂.pow_succ_not_dvd
                (by norm_num) E₃.one_le E₃.pow_dvd E₃.pow_succ_not_dvd
                (115 / 384) (budget_twentyFour_mixed_fourNine block E₂.e E₃.e
                  he₂ he₃) (by unfold preE7CharacterRho; norm_num))
          · by_cases h27 : 3 ^ 3 ∣ blocks block
            · let E₂ := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
                Nat.prime_two h2
              let E₃ := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
                (by norm_num : Nat.Prime 3) h3
              have he₃ : 3 ≤ E₃.e := by
                simpa only [E₃, ExactPrimaryDivisor.ofPrimeDvd] using
                  (valuation_ge_of_pow_dvd block (by norm_num : Nat.Prime 3) h27)
              exact .inl (of_degreeFour_twentyFour_twoPrimary hTraceyHalf hTraceyLog
                hTraceyRefined hTraceyPerm block P hr hcomponent 2 E₂.e 3 E₃.e
                  Nat.prime_two E₂.one_le E₂.pow_dvd E₂.pow_succ_not_dvd
                  (by norm_num) E₃.one_le E₃.pow_dvd E₃.pow_succ_not_dvd
                  (185 / 576) (budget_twentyFour_mixed_twoTwentySeven block
                    E₂.e E₃.e E₂.one_le he₃)
                  (by unfold preE7CharacterRho; norm_num))
            · have hdvd : blocks block ∣ 2 ^ 1 * 3 ^ 2 :=
                dvd_binary_ternary_bounded (blocks_ne_zero block) hlarge5 h4 h27
              have hs2 : 2 ≤ blocks block := block.degrees_ge_two.2
              have hs18 : blocks block ≤ 18 := Nat.le_of_dvd (by norm_num) hdvd
              interval_cases hs : blocks block
              all_goals norm_num at hdvd
              all_goals norm_num at h2
              all_goals norm_num at h9
              all_goals exact .inl (of_degreeFour_twentyFour_eighteen hTraceyHalf
                hTraceyLog hTraceyRefined hTraceyPerm block P hr hcomponent hs)
        · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
            (by norm_num : Nat.Prime 3) h3
          have he : 2 ≤ E.e := by
            simpa only [E, ExactPrimaryDivisor.ofPrimeDvd] using
              (valuation_ge_of_pow_dvd block (by norm_num : Nat.Prime 3) h9)
          have hdvd : blocks block ∣ 3 ^ E.e := by
            simpa only [pow_zero, one_mul] using
              (dvd_binary_ternary_bounded (a := 0) (b := E.e)
                (blocks_ne_zero block) hlarge5
                  (by simpa only [Nat.zero_add, pow_one] using h2)
                  E.pow_succ_not_dvd)
          have hs : blocks block = 3 ^ E.e := Nat.dvd_antisymm hdvd E.pow_dvd
          exact .inl (of_degreeFour_twentyFour_ternaryPrimePowerTwo hTraceyHalf
            hTraceyLog hTraceyRefined hTraceyPerm block P hr hcomponent E.e he hs)
      · by_cases h2048 : 2 ^ 11 ∣ blocks block
        · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
            Nat.prime_two (dvd_trans (by norm_num : 2 ∣ 2 ^ 11) h2048)
          have he : 11 ≤ E.e := by
            simpa only [E, ExactPrimaryDivisor.ofPrimeDvd] using
              (valuation_ge_of_pow_dvd block Nat.prime_two h2048)
          exact .inl (of_degreeFour_twentyFour_binaryEleven hTraceyHalf hTraceyLog
            hTraceyRefined hTraceyPerm block P hr hcomponent E.e he E.pow_dvd
              E.pow_succ_not_dvd)
        · have hdvd : blocks block ∣ 2 ^ 10 * 3 ^ 1 :=
            dvd_binary_ternary_bounded (blocks_ne_zero block) hlarge5 h2048 h9
          let k := Classical.choose h3
          have hk : blocks block = 3 * k := by
            have hk0 := Classical.choose_spec h3
            change blocks block = 3 * k at hk0
            simpa [Nat.mul_comm] using hk0
          have hkdiv : k ∣ 2 ^ 10 := by
            have hmul : 3 * k ∣ 3 * 2 ^ 10 := by
              rw [hk] at hdvd
              simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hdvd
            exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) hmul
          let a := Classical.choose ((Nat.dvd_prime_pow Nat.prime_two).mp hkdiv)
          have haspec := Classical.choose_spec
            ((Nat.dvd_prime_pow Nat.prime_two).mp hkdiv)
          exact .inr ⟨Or.inl (Or.inr ⟨a, haspec.1, by rw [hk, haspec.2]⟩)⟩
    · by_cases h512 : 2 ^ 9 ∣ blocks block
      · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
          Nat.prime_two (dvd_trans (by norm_num : 2 ∣ 2 ^ 9) h512)
        have he : 9 ≤ E.e := by
          simpa only [E, ExactPrimaryDivisor.ofPrimeDvd] using
            (valuation_ge_of_pow_dvd block Nat.prime_two h512)
        have hdvd : blocks block ∣ 2 ^ E.e := by
          simpa only [pow_zero, mul_one] using
            (dvd_binary_ternary_bounded (a := E.e) (b := 0)
              (blocks_ne_zero block) hlarge5 E.pow_succ_not_dvd
                (by simpa only [Nat.zero_add, pow_one] using h3))
        have hs : blocks block = 2 ^ E.e := Nat.dvd_antisymm hdvd E.pow_dvd
        exact .inl (of_degreeFour_twentyFour_binaryPrimePowerNine hTraceyHalf
          hTraceyLog hTraceyRefined hTraceyPerm block P hr hcomponent E.e he hs)
      · have hdvd : blocks block ∣ 2 ^ 8 := by
          simpa only [pow_zero, mul_one] using
            (dvd_binary_ternary_bounded (a := 8) (b := 0)
              (blocks_ne_zero block) hlarge5 h512
                (by simpa only [Nat.zero_add, pow_one] using h3))
        let a := Classical.choose ((Nat.dvd_prime_pow Nat.prime_two).mp hdvd)
        have haspec := Classical.choose_spec
          ((Nat.dvd_prime_pow Nat.prime_two).mp hdvd)
        have hsa : blocks block = 2 ^ a := haspec.2
        have ha1 : 1 ≤ a := by
          by_contra ha0
          have ha0' : a = 0 := by omega
          have hs1 : blocks block = 1 := by simpa [ha0'] using hsa
          have hs2 := block.degrees_ge_two.2
          change 2 ≤ blocks block at hs2
          omega
        exact .inr ⟨Or.inl (Or.inl ⟨a, ha1, haspec.1, hsa⟩)⟩

end ComponentSource
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
