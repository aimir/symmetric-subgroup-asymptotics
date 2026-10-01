import SymmetricSubgroupAsymptotics.Non2PreE7Sns2SecondaryNumerics

/-!
# Complete numerical/SNS2 closure of the pre-E7 residual

This module combines the disjoint physical cover, its exact local rows, the
ordinary main menu, and the globally correlated SNS2 secondary estimate.
The only remaining family-specific input is the final residual row against
the enlarged ordinary-plus-SNS2 first-owner predicate.
-/

set_option autoImplicit false
noncomputable section
open Filter

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

variable
  (Residual : ∀ w (U : PreE7NonPairActionClass w),
    PreE7NumericalSns2ResidualChoice w U)

/-- The exact no-pair/no-C3 residual ratio is covered by the disjoint
ordinary-numerical, SNS2, and terminal catalogue. -/
theorem preE7NumericalSns2_physicalBound :
    GrowingQuotientAdditiveExceptionalPhysicalBound
      preE7NoPairNoC3ResidualRatio 3
      (preE7NumericalSns2D Residual) preE7NumericalSns2T
      preE7NumericalSns2X preE7NumericalSns2A
      (preE7NumericalSns2V Residual) (preE7NumericalSns2Eta Residual)
      (preE7NumericalSns2Delta Residual)
      (preE7NumericalSns2Cutoff Residual)
      (preE7NumericalSns2Alpha Residual) preE7NumericalSns2Theta :=
  growingQuotientAdditiveExceptionalPhysicalBound_of_local
    preE7NoPairNoC3ResidualRatio 3 (by omega)
    PreE7NoPairNoC3ResidualSubgroupSet
    preE7NumericalSns2Action preE7NumericalSns2Predicate
    (preE7NumericalSns2D Residual) preE7NumericalSns2T
    preE7NumericalSns2X preE7NumericalSns2A
    (preE7NumericalSns2V Residual) (preE7NumericalSns2Eta Residual)
    (preE7NumericalSns2Delta Residual)
    (preE7NumericalSns2Cutoff Residual)
    (preE7NumericalSns2Alpha Residual) preE7NumericalSns2Theta
    (Filter.Eventually.of_forall (fun n => by
      rw [preE7NoPairNoC3ResidualRatio_eq_subgroupSet n]))
    preE7NumericalSns2_physical_cover
    (preE7NumericalSns2_local_bound Residual)

/-- The enlarged numerical/SNS2 catalogue gives the complete forward
estimate for the exact final pre-E7 residual. -/
noncomputable def preE7NumericalSns2_exponentialForwardEstimate
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput)
    (hOuter : SemisimpleOuterFactorPermutationBound) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7NoPairNoC3ResidualRatio :=
  growingQuotientAdditiveExceptional_exponentialForwardEstimate_of_secondary
    preE7NoPairNoC3ResidualRatio 3
    (preE7NumericalSns2D Residual) preE7NumericalSns2T
    preE7NumericalSns2X preE7NumericalSns2A
    (preE7NumericalSns2V Residual) (preE7NumericalSns2Eta Residual)
    (preE7NumericalSns2Delta Residual)
    (preE7NumericalSns2Cutoff Residual)
    (preE7NumericalSns2Alpha Residual) preE7NumericalSns2Theta
    (by norm_num [preE7CharacterRho])
    (by norm_num [preE7CharacterRho]) (by omega)
    (preE7NumericalSns2D_nonneg Residual) preE7NumericalSns2A_pos
    (preE7NumericalSns2_parameterBound Residual)
    (preE7NumericalSns2_mainMenu Residual hLMM) hcoarse
    (preE7NumericalSns2_secondary hLMM hcoarse hFS hOuter)
    (preE7NumericalSns2_physicalBound Residual)

/-- Publication-facing T1 boundary after all ordinary numerical owners and
SNS2 have been discharged. -/
theorem T1_of_preE7_numericalSns2_residual
    (Residual : ∀ w (U : PreE7NonPairActionClass w),
      PreE7NumericalSns2ResidualChoice w U)
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
    (preE7NumericalSns2_exponentialForwardEstimate Residual
      hLMM hcoarse hFS hOuter)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
