import SymmetricSubgroupAsymptotics.DegreeFourSixteenZeroCoreColdData
import SymmetricSubgroupAsymptotics.FixedColdRankSourceInstallation
import SymmetricSubgroupAsymptotics.FixedAffineSixteenColdNumerics

/-! Complete actual source for all degree4/count16 zero-ternary-core
frames. No primitive16 locator or substitute finite-frame premise occurs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre) [Nontrivial block.Fibre]

def degreeFourSixteenZeroCoreColdSource
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre=4) (hs : Nat.card block.Points=16)
    (hzero : degreeFourTernaryCore block P=⊥) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let S := degreeFourSixteenZeroCoreColdData block P hTraceyPerm hr hs hzero
  have hw : w=64 := by rw [width_eq block,hr,hs]
  have hp : PreE7CharacterEntryParameters preE7CharacterRho w S.v
      (153/50) (1/100) (401/200) (1013/200) 0 := by
    change PreE7CharacterEntryParameters preE7CharacterRho w (Nat.card block.Points)
      (153/50) (1/100) (401/200) (1013/200) 0
    have hp0 : PreE7CharacterEntryParameters preE7CharacterRho 64 16
        (153/50) (1/100) (401/200) (1013/200) 0 := by
      constructor <;> norm_num [preE7CharacterRho,halfDegree]
    simpa only [hw,hs] using hp0
  let M : S.NumericalMargin := FixedColdRankSourceInstallation.numericalMargin
    S 32 (77+2^45) 5929 9394 (by omega) (by decide) (by omega)
    (153/50) (1/100) (401/200) (1013/200)
    rfl rfl (by change (51/200 : ℝ)*(12 : ℕ)=153/50; norm_num) rfl rfl hp (by
      intro b
      have hh := FixedAffineSixteenColdNumerics.two_rpow_twelveThousandFiveHundred_le_menuMass b
      rw [Real.rpow_natCast] at hh
      have hg := (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by decide : 9394 ≤ 12500)).trans hh
      simpa only [hw] using hg)
  exact .inr (.inr (S.toResidualChoice M))

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
