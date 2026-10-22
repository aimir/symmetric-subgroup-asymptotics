import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineFullTraceSource
import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineOrderTraceBudget
import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineOrderTracePilot

/-! Every actual primitive affine action of degree81 has a complete source
from the full linear-order trace budget. Solubility is irrelevant to this
consumer, so no degree81 soluble-complement cube or composition theorem is
required. This proves the needed source, not the stronger order inequality. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
namespace CFSGPrimitiveAffineEightyOneOrderSource
open PrimitiveAffineProfile

private theorem exponent_margin
    (U : PreE7NonPairActionClass 81)
    (P : PrimitiveAffineProfile (preE7NonPairAction 81 U) (Fin 81))
    (hp : MulAction.IsPreprimitive (preE7NonPairAction 81 U) (Fin 81))
    (x : Fin 81) (T : FixedTargetCompositionTrace (P.complement x)) :
    preE7CharacterRho * 81 ≤ ((evenWidth 81 : ℝ) - 2) / 8 -
      (fixedTargetCompositionGamma * T.envelope.abelianLength + P.bottomFullSlope) := by
  have hlen := P.complementTrace_abelianLength_le_fullLinearOmega hp x
    (p := 3) (d := 4) Nat.prime_three (by decide) (by norm_num) T
  rw [CFSGPrimitiveAffineOrderTracePilot.selected_GL_four_three] at hlen
  have hlenR : (T.envelope.abelianLength : ℝ) ≤ 17 := by exact_mod_cast hlen
  have hg0 : 0 ≤ fixedTargetCompositionGamma := by
    unfold fixedTargetCompositionGamma
    exact div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)
  have hg : fixedTargetCompositionGamma < (8 : ℝ) / 15 := by
    unfold fixedTargetCompositionGamma
    have h := RepeatedMarkerProfileBound.logb_two_three_lt
    linarith
  have hb := P.bottomFullSlope_le_fixedTargetGamma
  have he := mul_le_mul_of_nonneg_left hlenR hg0
  norm_num [preE7CharacterRho, evenWidth, halfDegree]
  nlinarith

noncomputable def source
    (U : PreE7NonPairActionClass 81)
    (hp : MulAction.IsPreprimitive (preE7NonPairAction 81 U) (Fin 81))
    (P : PrimitiveAffineProfile (preE7NonPairAction 81 U) (Fin 81)) :
    PreE7RankTailOwnerSourceData 81 U := by
  let x : Fin 81 := ⟨0, by decide⟩
  let C := P.elementaryChart hp
  let T := FixedTargetCompositionTrace.canonical (P.complement x)
  exact CFSGPrimitiveAffineFullTraceSource.rankTailOwnerSourceDataOfMargin
    (by decide) (by decide) hp P x C T (exponent_margin U P hp x T)

end CFSGPrimitiveAffineEightyOneOrderSource
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
