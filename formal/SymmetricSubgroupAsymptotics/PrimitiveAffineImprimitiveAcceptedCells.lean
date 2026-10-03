import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveMixedDivisor

/-!
# Accepted finite cells in the small affine table

The cells here are the finite nonexception entries left after the divisibility
arguments.  They are proved from the actual chief tower, using exact
prime-power or mixed-divisor Tracey rates.  No action census is used.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
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

private theorem degreeFive_threePrimary_budget :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate (blocks block) 3 1) 20 ≤
      (22 / 45 : ℝ) * blocks block := by
  have h2 := traceyPrimaryRate_nonmatching_le (blocks block) 3 1 2 3
    (by norm_num) (by norm_num) (by norm_num)
  have h5 := traceyPrimaryRate_nonmatching_le (blocks block) 3 1 5 3
    (by norm_num) (by norm_num) (by norm_num)
  have h := refinedWeightedFactorBudget_twenty_le_of_rate_le
    (ActualWreathCompressionTower.traceyPrimaryRate (blocks block) 3 1)
    ((blocks block : ℝ) / 3) h2 h5
    (ActualWreathCompressionTower.traceyPrimaryRate_nonneg
      (blocks block) 3 1 5)
  have heq : (22 / 15 : ℝ) * ((blocks block : ℝ) / 3) =
      (22 / 45 : ℝ) * blocks block := by ring
  rw [← heq]
  exact h

/-- Degree five at any even block count with exact ternary valuation one.
This includes the finite accepted counts `6,12,24,48`. -/
noncomputable def of_degreeFive_even_threePrimary
    (hr : Nat.card block.Fibre = 5)
    (hdiv : 3 ∣ blocks block) (hmax : ¬ 9 ∣ blocks block)
    (heven : Even (blocks block)) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P 3 1 20 (by norm_num) (by norm_num)
      (by simpa using hdiv) (by simpa using hmax) (by norm_num)
  · have hprime : (Nat.card block.Fibre).Prime := by rw [hr]; norm_num
    have h := component_card_dvd_prime_mul_pred block P hprime
    simpa only [hr] using h
  · apply smallAffine_even_budget_margin 5 (blocks block) w
      (by simpa only [hr] using width_eq block)
      (by
        have hw := width_eq block
        rw [hr] at hw
        rw [hw]
        exact Even.mul_left heven 5) (22 / 45) _
    · unfold preE7CharacterRho
      norm_num
    · exact degreeFive_threePrimary_budget block

private theorem degreeFive_primePower_eight_budget :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimePowerRate 2 3) 20 ≤
      (52 / 15 : ℝ) := by
  rw [refinedWeightedFactorBudget_twenty]
  simp only [ActualWreathCompressionTower.traceyPrimePowerRate,
    if_neg (by norm_num : (5 : ℕ) ≠ 2)]
  have hslope := logb_two_five_div_five_lt_seven_fifteenths.le
  norm_num [Nat.choose] at hslope ⊢
  linarith

private theorem degreeFive_primePower_sixteen_budget :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimePowerRate 2 4) 20 ≤
      (97 / 15 : ℝ) := by
  rw [refinedWeightedFactorBudget_twenty]
  simp only [ActualWreathCompressionTower.traceyPrimePowerRate,
    if_neg (by norm_num : (5 : ℕ) ≠ 2)]
  have hslope := logb_two_five_div_five_lt_seven_fifteenths.le
  norm_num [Nat.choose] at hslope ⊢
  linarith

noncomputable def of_degreeFive_eightBlocks
    (hr : Nat.card block.Fibre = 5) (hs : blocks block = 8) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  have hs' : Nat.card block.Points = 8 := by simpa only [blocks] using hs
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimePower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P 2 3 20 (by norm_num) (by norm_num) hs (by norm_num)
  · have hprime : (Nat.card block.Fibre).Prime := by rw [hr]; norm_num
    have h := component_card_dvd_prime_mul_pred block P hprime
    simpa only [hr] using h
  · apply smallAffine_even_budget_margin 5 (blocks block) w
      (by simpa only [hr] using width_eq block)
      (by
        have hw := width_eq block
        rw [hr, hs'] at hw
        rw [hw]
        decide) (13 / 30) _
    · unfold preE7CharacterRho
      norm_num
    · have h := degreeFive_primePower_eight_budget
      rw [hs]
      norm_num at h ⊢
      exact h

noncomputable def of_degreeFive_sixteenBlocks
    (hr : Nat.card block.Fibre = 5) (hs : blocks block = 16) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  have hs' : Nat.card block.Points = 16 := by simpa only [blocks] using hs
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimePower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P 2 4 20 (by norm_num) (by norm_num) hs (by norm_num)
  · have hprime : (Nat.card block.Fibre).Prime := by rw [hr]; norm_num
    have h := component_card_dvd_prime_mul_pred block P hprime
    simpa only [hr] using h
  · apply smallAffine_even_budget_margin 5 (blocks block) w
      (by simpa only [hr] using width_eq block)
      (by
        have hw := width_eq block
        rw [hr, hs'] at hw
        rw [hw]
        decide) (97 / 240) _
    · unfold preE7CharacterRho
      norm_num
    · have h := degreeFive_primePower_sixteen_budget
      rw [hs]
      norm_num at h ⊢
      exact h

private theorem degreeNine_primePower_eight_budget :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimePowerRate 2 3) 432 ≤
      (243 / 32 : ℝ) := by
  rw [refinedWeightedFactorBudget_fourThirtyTwo]
  unfold ActualWreathCompressionTower.traceyPrimePowerRate
  rw [if_pos rfl, if_neg (by norm_num : (3 : ℕ) ≠ 2)]
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  norm_num at hgamma ⊢
  linarith

noncomputable def of_degreeNine_eightBlocks
    (hr : Nat.card block.Fibre = 9) (hs : blocks block = 8) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  have hs' : Nat.card block.Points = 8 := by simpa only [blocks] using hs
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimePower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P 2 3 432 (by norm_num) (by norm_num) hs (by norm_num)
  · exact component_card_dvd_432 block P hr
  · apply smallAffine_even_budget_margin 9 (blocks block) w
      (by simpa only [hr] using width_eq block)
      (by
        have hw := width_eq block
        rw [hr, hs'] at hw
        rw [hw]
        decide) (243 / 256) _
    · unfold preE7CharacterRho
      norm_num
    · have h := degreeNine_primePower_eight_budget
      rw [hs]
      norm_num at h ⊢
      exact h

private def degreeNine_twentyFourRate (p : ℕ) : ℝ :=
  min (ActualWreathCompressionTower.traceyPrimaryRate 24 2 3 p)
    (ActualWreathCompressionTower.traceyPrimaryRate 24 3 1 p)

private theorem degreeNine_twentyFour_budget :
    refinedWeightedFactorBudget degreeNine_twentyFourRate 432 ≤
      (665 / 768 : ℝ) * 24 := by
  rw [refinedWeightedFactorBudget_fourThirtyTwo]
  have h2 : degreeNine_twentyFourRate 2 ≤ (24 : ℝ) / 3 := by
    exact (min_le_right _ _).trans
      (traceyPrimaryRate_nonmatching_le 24 3 1 2 3 (by norm_num)
        (by norm_num) (by norm_num))
  have h3 : degreeNine_twentyFourRate 3 ≤ (24 : ℝ) / 8 := by
    exact (min_le_left _ _).trans
      (traceyPrimaryRate_nonmatching_le 24 2 3 3 8 (by norm_num)
        (by norm_num) (by norm_num))
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hr3 : 0 ≤ degreeNine_twentyFourRate 3 := by
    apply le_min <;>
      exact ActualWreathCompressionTower.traceyPrimaryRate_nonneg _ _ _ _
  calc
    _ ≤ 2 * ((24 : ℝ) / 3) + 3 * (17 / 32 : ℝ) * ((24 : ℝ) / 8) := by
      gcongr
    _ = (665 / 768 : ℝ) * 24 := by ring

noncomputable def of_degreeNine_twentyFourBlocks
    (hr : Nat.card block.Fibre = 9) (hs : blocks block = 24) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  have hs' : Nat.card block.Points = 24 := by simpa only [blocks] using hs
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_twoTraceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P 2 3 3 1 432 (by norm_num) (by norm_num)
      (by change 8 ∣ Nat.card block.Points; rw [hs']; norm_num)
      (by change ¬ 16 ∣ Nat.card block.Points; rw [hs']; norm_num)
      (by norm_num) (by norm_num)
      (by change 3 ∣ Nat.card block.Points; rw [hs']; norm_num)
      (by change ¬ 9 ∣ Nat.card block.Points; rw [hs']; norm_num)
      (by norm_num) (component_card_dvd_432 block P hr)
  apply smallAffine_even_budget_margin 9 (blocks block) w
    (by simpa only [hr] using width_eq block)
    (by
      have hw := width_eq block
      rw [hr, hs'] at hw
      rw [hw]
      decide) (665 / 768) _
  · unfold preE7CharacterRho
    norm_num
  · simpa only [blocks, hs', degreeNine_twentyFourRate] using
      degreeNine_twentyFour_budget

end ComponentSource
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
