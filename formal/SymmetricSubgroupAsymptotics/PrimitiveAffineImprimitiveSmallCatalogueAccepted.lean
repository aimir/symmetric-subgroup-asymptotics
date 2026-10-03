import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallCatalogueCapacity
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveMixedDivisor

/-!
# Accepted cells from the literal small-affine catalogue

The published catalogue retains the exact soluble point-stabilizer order.
For local degree eight this gives the component divisor `168`, and for local
degree sixteen the divisor `5760`.  These smaller literal orders close all
the accepted cells in the finite arithmetic table.  At degree eight and
three blocks the integer floor on the ternary capacity is essential.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

private theorem logb_three_add_fifth_logb_five_le :
    Real.logb 2 3 + Real.logb 2 5 / 5 ≤ (41 : ℝ) / 20 := by
  have hp : (3 : ℝ) ^ (20 : ℕ) * (5 : ℝ) ^ (4 : ℕ) ≤
      (2 : ℝ) ^ (41 : ℕ) := by norm_num
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (3 : ℝ) ^ (20 : ℕ) * (5 : ℝ) ^ (4 : ℕ)) hp
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
    Real.logb_pow, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at hlog
  norm_num at hlog ⊢
  linarith

private def rateEightTwelve (p : ℕ) : ℝ :=
  min (ActualWreathCompressionTower.traceyPrimaryRate 12 2 2 p)
    (ActualWreathCompressionTower.traceyPrimaryRate 12 3 1 p)

private theorem integralBudget_eight_three :
    integralRefinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimePowerRate 3 1) 168 ≤
      (41 / 50 : ℝ) * 3 := by
  rw [integralRefinedWeightedFactorBudget_oneSixtyEight]
  simp only [ActualWreathCompressionTower.traceyPrimePowerRate]
  norm_num [Nat.choose]
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hseven := logb_two_seven_div_seven_lt_three_sevenths.le
  nlinarith

private theorem refinedBudget_eight_twelve :
    refinedWeightedFactorBudget rateEightTwelve 168 ≤
      (3 / 4 : ℝ) * 12 := by
  rw [refinedWeightedFactorBudget_oneSixtyEight]
  have h2 : rateEightTwelve 2 ≤ 4 := by
    have h := traceyPrimaryRate_nonmatching_le 12 3 1 2 3
      (by norm_num) (by norm_num) (by norm_num)
    norm_num at h
    exact (min_le_right _ _).trans h
  have h3 : rateEightTwelve 3 ≤ 3 := by
    have h := traceyPrimaryRate_nonmatching_le 12 2 2 3 4
      (by norm_num) (by norm_num) (by norm_num)
    norm_num at h
    exact (min_le_left _ _).trans h
  have h7 : rateEightTwelve 7 ≤ 3 := by
    have h := traceyPrimaryRate_nonmatching_le 12 2 2 7 4
      (by norm_num) (by norm_num) (by norm_num)
    norm_num at h
    exact (min_le_left _ _).trans h
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hseven := logb_two_seven_div_seven_lt_three_sevenths.le
  have hr3 : 0 ≤ rateEightTwelve 3 := by
    exact le_min
      (ActualWreathCompressionTower.traceyPrimaryRate_nonneg 12 2 2 3)
      (ActualWreathCompressionTower.traceyPrimaryRate_nonneg 12 3 1 3)
  have hr7 : 0 ≤ rateEightTwelve 7 := by
    exact le_min
      (ActualWreathCompressionTower.traceyPrimaryRate_nonneg 12 2 2 7)
      (ActualWreathCompressionTower.traceyPrimaryRate_nonneg 12 3 1 7)
  calc
    _ ≤ (3 / 2 : ℝ) * 4 + (17 / 32 : ℝ) * 3 + (3 / 7 : ℝ) * 3 := by
      gcongr
    _ ≤ (3 / 4 : ℝ) * 12 := by norm_num

private def rateSixteenSix (p : ℕ) : ℝ :=
  min (ActualWreathCompressionTower.traceyPrimaryRate 6 2 1 p)
    (ActualWreathCompressionTower.traceyPrimaryRate 6 3 1 p)

private def rateSixteenTwelve (p : ℕ) : ℝ :=
  min (ActualWreathCompressionTower.traceyPrimaryRate 12 2 2 p)
    (ActualWreathCompressionTower.traceyPrimaryRate 12 3 1 p)

private def rateSixteenTwentyFour (p : ℕ) : ℝ :=
  min (ActualWreathCompressionTower.traceyPrimaryRate 24 2 3 p)
    (ActualWreathCompressionTower.traceyPrimaryRate 24 3 1 p)

private def rateSixteenFortyEight (p : ℕ) : ℝ :=
  min (ActualWreathCompressionTower.traceyPrimaryRate 48 2 4 p)
    (ActualWreathCompressionTower.traceyPrimaryRate 48 3 1 p)

private theorem refinedBudget_sixteen_three :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimePowerRate 3 1) 5760 ≤
      (37 / 20 : ℝ) * 3 := by
  rw [refinedWeightedFactorBudget_fiveSevenSixty]
  simp only [ActualWreathCompressionTower.traceyPrimePowerRate]
  norm_num [Nat.choose]
  unfold fixedTargetCompositionGamma
  nlinarith [logb_three_add_fifth_logb_five_le]

private theorem refinedBudget_sixteen_six :
    refinedWeightedFactorBudget rateSixteenSix 5760 ≤
      (37 / 20 : ℝ) * 6 := by
  rw [refinedWeightedFactorBudget_fiveSevenSixty]
  have h2 : rateSixteenSix 2 ≤ 2 := by
    have h := traceyPrimaryRate_nonmatching_le 6 3 1 2 3
      (by norm_num) (by norm_num) (by norm_num)
    norm_num at h
    exact (min_le_right _ _).trans h
  have h3 : rateSixteenSix 3 ≤ 3 := by
    have h := traceyPrimaryRate_nonmatching_le 6 2 1 3 2
      (by norm_num) (by norm_num) (by norm_num)
    norm_num at h
    exact (min_le_left _ _).trans h
  have h5 : rateSixteenSix 5 ≤ 2 := by
    have h := traceyPrimaryRate_nonmatching_le 6 3 1 5 3
      (by norm_num) (by norm_num) (by norm_num)
    norm_num at h
    exact (min_le_right _ _).trans h
  have hr3 : 0 ≤ rateSixteenSix 3 := by
    exact le_min
      (ActualWreathCompressionTower.traceyPrimaryRate_nonneg 6 2 1 3)
      (ActualWreathCompressionTower.traceyPrimaryRate_nonneg 6 3 1 3)
  have hr5 : 0 ≤ rateSixteenSix 5 := by
    exact le_min
      (ActualWreathCompressionTower.traceyPrimaryRate_nonneg 6 2 1 5)
      (ActualWreathCompressionTower.traceyPrimaryRate_nonneg 6 3 1 5)
  have hgamma0 : 0 ≤ fixedTargetCompositionGamma := by
    unfold fixedTargetCompositionGamma
    exact div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)
  have hfive0 : 0 ≤ Real.logb 2 5 / 5 :=
    div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)
  calc
    _ ≤ (7 / 2 : ℝ) * 2 + 2 * fixedTargetCompositionGamma * 3 +
        (Real.logb 2 5 / 5) * 2 := by gcongr
    _ = 7 + 2 * (Real.logb 2 3 + Real.logb 2 5 / 5) := by
      unfold fixedTargetCompositionGamma
      ring
    _ ≤ (37 / 20 : ℝ) * 6 := by
      nlinarith [logb_three_add_fifth_logb_five_le]

private theorem budget5760_of_rate_bounds
    (rate : ℕ → ℝ) (s a b c : ℝ)
    (h2 : rate 2 ≤ a) (h3 : rate 3 ≤ b) (h5 : rate 5 ≤ c)
    (hr3 : 0 ≤ rate 3) (hr5 : 0 ≤ rate 5)
    (hnum : (7 / 2 : ℝ) * a + 2 * (17 / 32 : ℝ) * b +
      (7 / 15 : ℝ) * c ≤ (37 / 20 : ℝ) * s) :
    refinedWeightedFactorBudget rate 5760 ≤ (37 / 20 : ℝ) * s := by
  rw [refinedWeightedFactorBudget_fiveSevenSixty]
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hfive := logb_two_five_div_five_lt_seven_fifteenths.le
  have hgamma0 : 0 ≤ fixedTargetCompositionGamma := by
    unfold fixedTargetCompositionGamma
    exact div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)
  have hfive0 : 0 ≤ Real.logb 2 5 / 5 :=
    div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)
  calc
    _ ≤ (7 / 2 : ℝ) * a + 2 * fixedTargetCompositionGamma * rate 3 +
        (Real.logb 2 5 / 5) * rate 5 := by gcongr
    _ ≤ (7 / 2 : ℝ) * a + 2 * (17 / 32 : ℝ) * rate 3 +
        (7 / 15 : ℝ) * rate 5 := by gcongr
    _ ≤ (7 / 2 : ℝ) * a + 2 * (17 / 32 : ℝ) * b +
        (7 / 15 : ℝ) * c := by gcongr
    _ ≤ (37 / 20 : ℝ) * s := hnum

private theorem refinedBudget_sixteen_eight :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimePowerRate 2 3) 5760 ≤
      (37 / 20 : ℝ) * 8 := by
  apply budget5760_of_rate_bounds _ 8 3 1 1
      <;> simp [ActualWreathCompressionTower.traceyPrimePowerRate, Nat.choose]
      <;> norm_num

private theorem refinedBudget_sixteen_twelve :
    refinedWeightedFactorBudget rateSixteenTwelve 5760 ≤
      (37 / 20 : ℝ) * 12 := by
  apply budget5760_of_rate_bounds _ 12 4 3 3
  · have h := traceyPrimaryRate_nonmatching_le 12 3 1 2 3
        (by norm_num) (by norm_num) (by norm_num)
    norm_num at h
    exact (min_le_right _ _).trans h
  · have h := traceyPrimaryRate_nonmatching_le 12 2 2 3 4
        (by norm_num) (by norm_num) (by norm_num)
    norm_num at h
    exact (min_le_left _ _).trans h
  · have h := traceyPrimaryRate_nonmatching_le 12 2 2 5 4
        (by norm_num) (by norm_num) (by norm_num)
    norm_num at h
    exact (min_le_left _ _).trans h
  · exact le_min
      (ActualWreathCompressionTower.traceyPrimaryRate_nonneg 12 2 2 3)
      (ActualWreathCompressionTower.traceyPrimaryRate_nonneg 12 3 1 3)
  · exact le_min
      (ActualWreathCompressionTower.traceyPrimaryRate_nonneg 12 2 2 5)
      (ActualWreathCompressionTower.traceyPrimaryRate_nonneg 12 3 1 5)
  · norm_num

private theorem refinedBudget_sixteen_sixteen :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimePowerRate 2 4) 5760 ≤
      (37 / 20 : ℝ) * 16 := by
  apply budget5760_of_rate_bounds _ 16 6 1 1
      <;> simp [ActualWreathCompressionTower.traceyPrimePowerRate, Nat.choose]
      <;> norm_num

private theorem refinedBudget_sixteen_twentyFour :
    refinedWeightedFactorBudget rateSixteenTwentyFour 5760 ≤
      (37 / 20 : ℝ) * 24 := by
  apply budget5760_of_rate_bounds _ 24 8 3 3
  · have h := traceyPrimaryRate_nonmatching_le 24 3 1 2 3
        (by norm_num) (by norm_num) (by norm_num)
    norm_num at h
    exact (min_le_right _ _).trans h
  · have h := traceyPrimaryRate_nonmatching_le 24 2 3 3 8
        (by norm_num) (by norm_num) (by norm_num)
    norm_num at h
    exact (min_le_left _ _).trans h
  · have h := traceyPrimaryRate_nonmatching_le 24 2 3 5 8
        (by norm_num) (by norm_num) (by norm_num)
    norm_num at h
    exact (min_le_left _ _).trans h
  · exact le_min
      (ActualWreathCompressionTower.traceyPrimaryRate_nonneg 24 2 3 3)
      (ActualWreathCompressionTower.traceyPrimaryRate_nonneg 24 3 1 3)
  · exact le_min
      (ActualWreathCompressionTower.traceyPrimaryRate_nonneg 24 2 3 5)
      (ActualWreathCompressionTower.traceyPrimaryRate_nonneg 24 3 1 5)
  · norm_num

private theorem refinedBudget_sixteen_fortyEight :
    refinedWeightedFactorBudget rateSixteenFortyEight 5760 ≤
      (37 / 20 : ℝ) * 48 := by
  apply budget5760_of_rate_bounds _ 48 16 3 3
  · have h := traceyPrimaryRate_nonmatching_le 48 3 1 2 3
        (by norm_num) (by norm_num) (by norm_num)
    norm_num at h
    exact (min_le_right _ _).trans h
  · have h := traceyPrimaryRate_nonmatching_le 48 2 4 3 16
        (by norm_num) (by norm_num) (by norm_num)
    norm_num at h
    exact (min_le_left _ _).trans h
  · have h := traceyPrimaryRate_nonmatching_le 48 2 4 5 16
        (by norm_num) (by norm_num) (by norm_num)
    norm_num at h
    exact (min_le_left _ _).trans h
  · exact le_min
      (ActualWreathCompressionTower.traceyPrimaryRate_nonneg 48 2 4 3)
      (ActualWreathCompressionTower.traceyPrimaryRate_nonneg 48 3 1 3)
  · exact le_min
      (ActualWreathCompressionTower.traceyPrimaryRate_nonneg 48 2 4 5)
      (ActualWreathCompressionTower.traceyPrimaryRate_nonneg 48 3 1 5)
  · norm_num

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

noncomputable def of_degreeEight_threeBlocks
    (D : PublishedPrimitiveAffineSmallCatalogueData)
    (hr : Nat.card block.Fibre = 8) (hs : blocks block = 3) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  by_cases hsolvable : IsSolvable (P.complement (origin block))
  · letI : Nontrivial block.Fibre :=
      Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
    have hs' : Nat.card block.Points = 3 := by simpa only [blocks] using hs
    apply of_integralTraceyPrimePower hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P 3 1 168 (by norm_num) (by norm_num)
      (by rw [hs']; norm_num) (by norm_num)
      (component_card_dvd_168_of_degreeEight_soluble D block P hr hsolvable)
    apply smallAffine_even_budget_margin 8 (blocks block) w
      (by simpa only [hr] using width_eq block)
      (by
        have hw := width_eq block
        rw [hr, hs'] at hw
        rw [hw]
        decide)
      (41 / 50) _
    · unfold preE7CharacterRho
      norm_num
    · simpa only [hs] using integralBudget_eight_three
  · exact of_degreeEight_nonsoluble hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P D hr hsolvable

noncomputable def of_degreeEight_twelveBlocks
    (D : PublishedPrimitiveAffineSmallCatalogueData)
    (hr : Nat.card block.Fibre = 8) (hs : blocks block = 12) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  by_cases hsolvable : IsSolvable (P.complement (origin block))
  · letI : Nontrivial block.Fibre :=
      Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
    have hs' : Nat.card block.Points = 12 := by simpa only [blocks] using hs
    apply of_twoTraceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
      block P 2 2 3 1 168 (by norm_num) (by norm_num)
      (by change 4 ∣ blocks block; rw [hs]; norm_num)
      (by change ¬ 8 ∣ blocks block; rw [hs]; norm_num)
      (by norm_num) (by norm_num)
      (by change 3 ∣ blocks block; rw [hs]; norm_num)
      (by change ¬ 9 ∣ blocks block; rw [hs]; norm_num)
      (by norm_num)
      (component_card_dvd_168_of_degreeEight_soluble D block P hr hsolvable)
    apply smallAffine_even_budget_margin 8 (blocks block) w
      (by simpa only [hr] using width_eq block)
      (by
        have hw := width_eq block
        rw [hr, hs'] at hw
        rw [hw]
        decide)
      (3 / 4) _
    · unfold preE7CharacterRho
      norm_num
    · simpa only [blocks, hs, rateEightTwelve] using refinedBudget_eight_twelve
  · exact of_degreeEight_nonsoluble hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P D hr hsolvable

private noncomputable def degreeSixteen_primePower
    (D : PublishedPrimitiveAffineSmallCatalogueData)
    (hr : Nat.card block.Fibre = 16)
    (q e s : ℕ) (hq : q.Prime) (he : 1 ≤ e)
    (hs : blocks block = s) (hspp : s = q ^ e)
    (hbudget : refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimePowerRate q e) 5760 ≤
      (37 / 20 : ℝ) * s) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  by_cases hsolvable : IsSolvable (P.complement (origin block))
  · letI : Nontrivial block.Fibre :=
      Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
    have hs' : Nat.card block.Points = s := by simpa only [blocks] using hs
    apply of_traceyPrimePower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
      block P q e 5760 hq he (by rw [hs', hspp]) (by norm_num)
      (component_card_dvd_5760_of_degreeSixteen_soluble D block P hr hsolvable)
    apply smallAffine_even_budget_margin 16 (blocks block) w
      (by simpa only [hr] using width_eq block)
      (by
        have hw := width_eq block
        rw [hr, hs'] at hw
        rw [hw]
        exact ⟨8 * s, by omega⟩)
      (37 / 20) _
    · unfold preE7CharacterRho
      norm_num
    · simpa only [hs] using hbudget
  · exact of_degreeSixteen_nonsoluble hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P D hr hsolvable

private noncomputable def degreeSixteen_twoPrimary
    (D : PublishedPrimitiveAffineSmallCatalogueData)
    (hr : Nat.card block.Fibre = 16)
    (a s : ℕ) (ha : 1 ≤ a) (hs : blocks block = s)
    (h2div : 2 ^ a ∣ s) (h2max : ¬ 2 ^ (a + 1) ∣ s)
    (h3div : 3 ∣ s) (h3max : ¬ 9 ∣ s)
    (rate : ℕ → ℝ)
    (hrate : rate = fun p => min
      (ActualWreathCompressionTower.traceyPrimaryRate s 2 a p)
      (ActualWreathCompressionTower.traceyPrimaryRate s 3 1 p))
    (hbudget : refinedWeightedFactorBudget rate 5760 ≤
      (37 / 20 : ℝ) * s) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  by_cases hsolvable : IsSolvable (P.complement (origin block))
  · letI : Nontrivial block.Fibre :=
      Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
    have hs' : Nat.card block.Points = s := by simpa only [blocks] using hs
    apply of_twoTraceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
      block P 2 a 3 1 5760 (by norm_num) ha
      (by simpa only [hs] using h2div)
      (by simpa only [hs] using h2max)
      (by norm_num) (by norm_num)
      (by simpa only [hs] using h3div)
      (by simpa only [hs] using h3max)
      (by norm_num)
      (component_card_dvd_5760_of_degreeSixteen_soluble D block P hr hsolvable)
    apply smallAffine_even_budget_margin 16 (blocks block) w
      (by simpa only [hr] using width_eq block)
      (by
        have hw := width_eq block
        rw [hr, hs'] at hw
        rw [hw]
        exact ⟨8 * s, by omega⟩)
      (37 / 20) _
    · unfold preE7CharacterRho
      norm_num
    · rw [hrate] at hbudget
      simpa only [hs] using hbudget
  · exact of_degreeSixteen_nonsoluble hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P D hr hsolvable

noncomputable def of_degreeSixteen_threeBlocks
    (D : PublishedPrimitiveAffineSmallCatalogueData)
    (hr : Nat.card block.Fibre = 16) (hs : blocks block = 3) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P :=
  degreeSixteen_primePower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P D hr 3 1 3 (by norm_num) (by norm_num) hs (by norm_num)
      refinedBudget_sixteen_three

noncomputable def of_degreeSixteen_sixBlocks
    (D : PublishedPrimitiveAffineSmallCatalogueData)
    (hr : Nat.card block.Fibre = 16) (hs : blocks block = 6) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P :=
  degreeSixteen_twoPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P D hr 1 6 (by norm_num) hs (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) rateSixteenSix rfl refinedBudget_sixteen_six

noncomputable def of_degreeSixteen_eightBlocks
    (D : PublishedPrimitiveAffineSmallCatalogueData)
    (hr : Nat.card block.Fibre = 16) (hs : blocks block = 8) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P :=
  degreeSixteen_primePower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P D hr 2 3 8 (by norm_num) (by norm_num) hs (by norm_num)
      refinedBudget_sixteen_eight

noncomputable def of_degreeSixteen_twelveBlocks
    (D : PublishedPrimitiveAffineSmallCatalogueData)
    (hr : Nat.card block.Fibre = 16) (hs : blocks block = 12) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P :=
  degreeSixteen_twoPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P D hr 2 12 (by norm_num) hs (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) rateSixteenTwelve rfl refinedBudget_sixteen_twelve

noncomputable def of_degreeSixteen_sixteenBlocks
    (D : PublishedPrimitiveAffineSmallCatalogueData)
    (hr : Nat.card block.Fibre = 16) (hs : blocks block = 16) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P :=
  degreeSixteen_primePower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P D hr 2 4 16 (by norm_num) (by norm_num) hs (by norm_num)
      refinedBudget_sixteen_sixteen

noncomputable def of_degreeSixteen_twentyFourBlocks
    (D : PublishedPrimitiveAffineSmallCatalogueData)
    (hr : Nat.card block.Fibre = 16) (hs : blocks block = 24) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P :=
  degreeSixteen_twoPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P D hr 3 24 (by norm_num) hs (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) rateSixteenTwentyFour rfl
        refinedBudget_sixteen_twentyFour

noncomputable def of_degreeSixteen_fortyEightBlocks
    (D : PublishedPrimitiveAffineSmallCatalogueData)
    (hr : Nat.card block.Fibre = 16) (hs : blocks block = 48) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P :=
  degreeSixteen_twoPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P D hr 4 48 (by norm_num) hs (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) rateSixteenFortyEight rfl
        refinedBudget_sixteen_fortyEight

end ComponentSource
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
