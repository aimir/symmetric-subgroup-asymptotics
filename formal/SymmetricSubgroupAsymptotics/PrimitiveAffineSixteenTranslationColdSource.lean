import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTranslationColdData
import SymmetricSubgroupAsymptotics.FixedColdRankSourceInstallation
import SymmetricSubgroupAsymptotics.FixedAffineSixteenColdNumerics

/-! Both fixed affine16 exceptional translation cells have a complete
source on the original action. No soluble complement locator, constituent
list, or published16 classification is a parameter. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre) [Nontrivial block.Fibre]

/-- The actual two-block affine16 cell, retaining all original normals. -/
def sixteenTwoBlockColdSource
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre=16) (hs : Nat.card block.Points=2) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let S := sixteenTwoBlockColdData block P hTraceyPerm hr hs
  have hw : w=32 := by rw [width_eq block,hr,hs]
  have hc : Fintype.card block.Points=2 := by simpa only [Fintype.card_eq_nat_card] using hs
  have hp : PreE7CharacterEntryParameters preE7CharacterRho w S.v
      (51/50) (1/100) (401/200) (121/40) 0 := by
    change PreE7CharacterEntryParameters preE7CharacterRho w (8*Fintype.card block.Points)
      (51/50) (1/100) (401/200) (121/40) 0
    simpa only [hw,hc,Nat.reduceMul] using FixedAffineSixteenColdNumerics.parameters_two
  let M : S.NumericalMargin := FixedColdRankSourceInstallation.numericalMargin
    S 16 (39+2^31) 1521 2730 (by omega) (by decide) (by omega)
    (51/50) (1/100) (401/200) (121/40)
    rfl rfl (sixteenTwoBlockColdData_eta block P hTraceyPerm hr hs) rfl rfl hp (by
      intro b
      have hh := WidthThirtyTwoBinaryRankTailResidual.two_rpow_fiveThousand_le_menuMass
        (w := 32) rfl b
      rw [Real.rpow_natCast] at hh
      have hg := (pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2)
        (by decide : 2730≤5000)).trans hh
      simpa only [hw] using hg)
  exact .inr (.inr (S.toResidualChoice M))

/-- The actual four-block affine16 cell, retaining all original normals. -/
def sixteenFourBlockColdSource
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre=16) (hs : Nat.card block.Points=4) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let S := sixteenFourBlockColdData block P hTraceyPerm hr hs
  have hw : w=64 := by rw [width_eq block,hr,hs]
  have hc : Fintype.card block.Points=4 := by simpa only [Fintype.card_eq_nat_card] using hs
  have hp : PreE7CharacterEntryParameters preE7CharacterRho w S.v
      (51/25) (1/100) (801/200) (1209/200) 0 := by
    change PreE7CharacterEntryParameters preE7CharacterRho w (8*Fintype.card block.Points)
      (51/25) (1/100) (801/200) (1209/200) 0
    simpa only [hw,hc,Nat.reduceMul] using FixedAffineSixteenColdNumerics.parameters_four
  let M : S.NumericalMargin := FixedColdRankSourceInstallation.numericalMargin
    S 32 (81+2^65) 6561 11826 (by omega) (by decide) (by omega)
    (51/25) (1/100) (801/200) (1209/200)
    rfl rfl (sixteenFourBlockColdData_eta block P hTraceyPerm hr hs) rfl rfl hp (by
      intro b
      have hh := FixedAffineSixteenColdNumerics.two_rpow_twelveThousandFiveHundred_le_menuMass b
      rw [Real.rpow_natCast] at hh
      have hg := (pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2)
        (by decide : 11826≤12500)).trans hh
      simpa only [hw] using hg)
  exact .inr (.inr (S.toResidualChoice M))

/-- Both formerly exceptional soluble cells are covered by the SAME
actual-kernel transfer; the theorem even permits nonsoluble complements. -/
def sixteenExceptionalTranslationColdSource
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre=16)
    (hs : Nat.card block.Points=2 ∨ Nat.card block.Points=4) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  apply Classical.choice
  rcases hs with hs | hs
  · exact ⟨sixteenTwoBlockColdSource block P hTraceyPerm hr hs⟩
  · exact ⟨sixteenFourBlockColdSource block P hTraceyPerm hr hs⟩

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
