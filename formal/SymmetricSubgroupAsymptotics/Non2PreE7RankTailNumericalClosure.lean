import SymmetricSubgroupAsymptotics.Non2PreE7RankTailSecondaryNumerics

/-!
# Complete numerical rank-tail closure of the pre-E7 residual

This combines the exact ordinary/B6/Y1/SNS2 physical cover with its main
menu and secondary estimate.  The only remaining family-specific input is
the terminal row against that enlarged first-owner predicate.
-/

set_option autoImplicit false
noncomputable section
open Filter

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

variable
  (lit : PreE7CharacterLiterature)
  (Residual : ∀ w (U : PreE7NonPairActionClass w),
    PreE7NumericalRankTailResidualChoice w U)

/-- The exact no-pair/no-C3 residual ratio is covered by the disjoint
ordinary, B6, Y1, SNS2, and terminal catalogue. -/
theorem preE7NumericalRankTail_physicalBound :
    GrowingQuotientAdditiveExceptionalPhysicalBound
      preE7NoPairNoC3ResidualRatio 3
      (preE7NumericalRankTailD Residual)
      (preE7NumericalRankTailT lit) (preE7NumericalRankTailX lit)
      preE7NumericalRankTailA (preE7NumericalRankTailV Residual)
      (preE7NumericalRankTailEta Residual)
      (preE7NumericalRankTailDelta Residual)
      (preE7NumericalRankTailCutoff Residual)
      (preE7NumericalRankTailAlpha Residual)
      preE7NumericalRankTailTheta :=
  growingQuotientAdditiveExceptionalPhysicalBound_of_local
    preE7NoPairNoC3ResidualRatio 3 (by omega)
    PreE7NoPairNoC3ResidualSubgroupSet
    preE7NumericalRankTailAction preE7NumericalRankTailPredicate
    (preE7NumericalRankTailD Residual)
    (preE7NumericalRankTailT lit) (preE7NumericalRankTailX lit)
    preE7NumericalRankTailA (preE7NumericalRankTailV Residual)
    (preE7NumericalRankTailEta Residual)
    (preE7NumericalRankTailDelta Residual)
    (preE7NumericalRankTailCutoff Residual)
    (preE7NumericalRankTailAlpha Residual)
    preE7NumericalRankTailTheta
    (Filter.Eventually.of_forall (fun n => by
      rw [preE7NoPairNoC3ResidualRatio_eq_subgroupSet n]))
    preE7NumericalRankTail_physical_cover
    (preE7NumericalRankTail_local_bound lit Residual)

/-- The enlarged rank-tail catalogue gives the complete forward estimate
for the exact final pre-E7 residual. -/
noncomputable def preE7NumericalRankTail_exponentialForwardEstimate
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput)
    (hOuter : SemisimpleOuterFactorPermutationBound) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7NoPairNoC3ResidualRatio :=
  growingQuotientAdditiveExceptional_exponentialForwardEstimate_of_secondary
    preE7NoPairNoC3ResidualRatio 3
    (preE7NumericalRankTailD Residual)
    (preE7NumericalRankTailT lit) (preE7NumericalRankTailX lit)
    preE7NumericalRankTailA (preE7NumericalRankTailV Residual)
    (preE7NumericalRankTailEta Residual)
    (preE7NumericalRankTailDelta Residual)
    (preE7NumericalRankTailCutoff Residual)
    (preE7NumericalRankTailAlpha Residual)
    preE7NumericalRankTailTheta
    (by norm_num [preE7CharacterRho])
    (by norm_num [preE7CharacterRho]) (by omega)
    (preE7NumericalRankTailD_nonneg Residual)
    preE7NumericalRankTailA_pos
    (preE7NumericalRankTail_parameterBound Residual)
    (preE7NumericalRankTail_mainMenu Residual hLMM) hcoarse
    (preE7NumericalRankTail_secondary lit hLMM hcoarse hFS hOuter)
    (preE7NumericalRankTail_physicalBound lit Residual)

/-- Publication-facing T1 boundary after all presently integrated numerical
and correlated rank-tail owners have been discharged. -/
theorem T1_of_preE7_numericalRankTail_residual
    (lit : PreE7CharacterLiterature)
    (Residual : ∀ w (U : PreE7NonPairActionClass w),
      PreE7NumericalRankTailResidualChoice w U)
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput)
    (hOuter : SemisimpleOuterFactorPermutationBound) : T1 :=
  T1_of_preE7_noPairNoC3_estimate hTracey hExceptional hChief hWeight
    hPrimitive h18 hKP
    (preE7NumericalRankTail_exponentialForwardEstimate lit Residual
      hLMM hcoarse hFS hOuter)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
