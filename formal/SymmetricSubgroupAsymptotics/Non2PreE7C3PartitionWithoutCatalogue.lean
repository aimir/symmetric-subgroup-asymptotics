import SymmetricSubgroupAsymptotics.Non2PreE7C3Partition
import SymmetricSubgroupAsymptotics.C3CompleteActualPhysicalContinuation

/-! Actual-consumer adapter without the composition catalogue. The original
physical families, rank caps, normal axes and numerical kernels are retained. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
open RepeatedC3TailPhysical RepeatedC3TailExtraction

noncomputable def preE7C3Covered_exponentialForwardEstimate_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hOuter : SemisimpleOuterFactorPermutationBound)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7C3CoveredRatio :=
  OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le
    (c3CompleteOrdinary_closedExponentialForwardEstimate_without_catalogue
      hChief hWeight hgen hindex published8 h18 hKP hOuter hcoarse) 0
    (fun n _ => preE7C3CoveredRatio_le_c3 n)

/-- A forward estimate for the exact complement after the regular-`C3` cut
closes the whole non-pair pre-`E7` residual. -/

noncomputable def preE7NonPair_exponentialForwardEstimate_of_noC3_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hOuter : SemisimpleOuterFactorPermutationBound)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (P : OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7NoPairNoC3ResidualRatio) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7NonPairResidualRatio := by
  let E := OrdinaryFrontierClosure.ExponentialForwardEstimate.add
    (preE7C3Covered_exponentialForwardEstimate_without_catalogue
      hChief hWeight hgen hindex published8 h18 hKP hOuter hcoarse) P
  exact OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le E 0
    (fun n _ => by rw [preE7NonPairResidualRatio_eq_c3_partition])

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
end
