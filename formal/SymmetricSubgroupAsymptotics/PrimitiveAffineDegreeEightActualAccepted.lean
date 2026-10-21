import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallCatalogueAccepted
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightActualComponentCapacity

/-! The accepted degree8 capacity cells use actual degree8 facts only.
All old numerical receipts and literal component towers remain unchanged. -/
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

private theorem refinedBudget_eight_binary
    (s e : ℕ) (he : 3 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate s 2 e) 168 ≤
      (5 / 6 : ℝ) * s := by
  rw [refinedWeightedFactorBudget_oneSixtyEight]
  have h2 := traceyPrimaryRate_two_matching_of_three_le s e he
  have hpow : 8 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num : 0 < 2) he
  have h3 := traceyPrimaryRate_nonmatching_le s 2 e 3 8
    (by norm_num) hpow (by norm_num)
  have h7 := traceyPrimaryRate_nonmatching_le s 2 e 7 8
    (by norm_num) hpow (by norm_num)
  have h3' : ActualWreathCompressionTower.traceyPrimaryRate s 2 e 3 ≤
      (s : ℝ) / 8 := by simpa using h3
  have h7' : ActualWreathCompressionTower.traceyPrimaryRate s 2 e 7 ≤
      (s : ℝ) / 8 := by simpa using h7
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hseven := logb_two_seven_div_seven_lt_three_sevenths.le
  have hr3 := ActualWreathCompressionTower.traceyPrimaryRate_nonneg s 2 e 3
  have hr7 := ActualWreathCompressionTower.traceyPrimaryRate_nonneg s 2 e 7
  calc
    _ ≤ (3 / 2 : ℝ) * ((s : ℝ) * (17 / 36)) +
        (17 / 32 : ℝ) * ((s : ℝ) / 8) +
        (3 / 7 : ℝ) * ((s : ℝ) / 8) := by gcongr
    _ ≤ (5 / 6 : ℝ) * s := by
      have hs : (0 : ℝ) ≤ s := by positivity
      norm_num
      linarith

namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightActual.ComponentSource
open _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.ComponentSource
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
    (hr : Nat.card block.Fibre = 8) (hs : blocks block = 3) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  by_cases hsolvable : IsSolvable (P.complement (origin block))
  · letI primitiveAffineDegreeEightActualAccepted_instance1 : Nontrivial block.Fibre :=
      Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
    have hs' : Nat.card block.Points = 3 := by simpa only [blocks] using hs
    apply of_integralTraceyPrimePower hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P 3 1 168 (by norm_num) (by norm_num)
      (by rw [hs']; norm_num) (by norm_num)
      (_root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightActual.component_card_dvd_168_of_degreeEight_soluble block P hr hsolvable)
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
  · exact _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightActual.ComponentSource.of_degreeEight_nonsoluble hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr hsolvable

noncomputable def of_degreeEight_twelveBlocks
    (hr : Nat.card block.Fibre = 8) (hs : blocks block = 12) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  by_cases hsolvable : IsSolvable (P.complement (origin block))
  · letI primitiveAffineDegreeEightActualAccepted_instance2 : Nontrivial block.Fibre :=
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
      (_root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightActual.component_card_dvd_168_of_degreeEight_soluble block P hr hsolvable)
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
  · exact _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightActual.ComponentSource.of_degreeEight_nonsoluble hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr hsolvable

noncomputable def of_degreeEight_primeTwo
    (hr : Nat.card block.Fibre = 8)
    (e : ℕ) (he : 3 ≤ e)
    (hdiv : 2 ^ e ∣ blocks block)
    (hmax : ¬ 2 ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  by_cases hsolvable : IsSolvable (P.complement (origin block))
  · letI primitiveAffineDegreeEightActualAccepted_instance3 : Nontrivial block.Fibre :=
      Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
    apply of_traceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
      block P 2 e 168 (by norm_num) (by omega) hdiv hmax (by norm_num)
      (_root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightActual.component_card_dvd_168_of_degreeEight_soluble block P hr hsolvable)
    apply smallAffine_even_budget_margin 8 (blocks block) w
      (by simpa only [hr] using width_eq block)
      (by
        have hw := width_eq block
        rw [hr] at hw
        rw [hw]
        exact ⟨4 * blocks block, by ring⟩)
      (5 / 6) _
    · unfold preE7CharacterRho
      norm_num
    · exact refinedBudget_eight_binary (blocks block) e he
  · exact _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightActual.ComponentSource.of_degreeEight_nonsoluble hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P hr hsolvable

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightActual.ComponentSource
end SymmetricSubgroupAsymptotics
