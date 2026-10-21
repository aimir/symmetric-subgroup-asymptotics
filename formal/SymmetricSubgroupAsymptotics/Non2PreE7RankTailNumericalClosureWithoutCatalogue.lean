import SymmetricSubgroupAsymptotics.Non2PreE7RankTailNumericalClosure
import SymmetricSubgroupAsymptotics.Non2PreE7SmallC3PacketNumericsWithoutCatalogue
import SymmetricSubgroupAsymptotics.Non2PreE7C3PartitionWithoutCatalogue

/-! Actual-consumer adapter without the composition catalogue. The original
physical families, rank caps, normal axes and numerical kernels are retained. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
open RepeatedC3TailPhysical RepeatedC3TailExtraction

theorem T1_of_preE7_numericalRankTail_residual_without_catalogue
    (lit : PreE7CharacterLiterature)
    (Residual : PreE7NumericalRankTailResidualData)
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput)
    (hOuter : SemisimpleOuterFactorPermutationBound) : T1 := by
  let Epacket := preE7SmallC3Packet_exponentialForwardEstimate_without_catalogue
    hChief hWeight hgen hindex published8 h18
  let Elarge := preE7NumericalRankTail_exponentialForwardEstimate lit Residual
    hLMM hcoarse hFS hOuter
  let Esum := OrdinaryFrontierClosure.ExponentialForwardEstimate.add
    Epacket Elarge
  let Eresidual := OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le
    Esum 0 (fun n _ => le_of_eq
      (preE7NoPairNoC3ResidualRatio_eq_packet_add_large n))
  exact T1_of_preE7_nonPair_estimate hTracey hExceptional
    (preE7NonPair_exponentialForwardEstimate_of_noC3_without_catalogue
      hChief hWeight hgen hindex published8 h18 hKP hOuter hcoarse Eresidual)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
end
