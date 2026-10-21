import SymmetricSubgroupAsymptotics.C1DegreeNineRankBudget
import SymmetricSubgroupAsymptotics.C1DegreeNineSourceRankWithoutCatalogue

/-! Install the proved orbitwise rank capacity on the unchanged source pattern. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
/-- The one-regular-`C3`, no-natural-`A4` pattern proves the retained
numerical source budget. -/
theorem C1DegreeNineSourcePattern.rankBudget_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {X : Type} [Fintype X] (J : Subgroup (Equiv.Perm X))
    (h : C1DegreeNineSourcePattern J) :
    C1DegreeNineRankBudget J := by
  unfold C1DegreeNineRankBudget
  obtain ⟨exceptional, hexceptional, hunique, hnoA4⟩ := h
  exact ternaryCharacterRank_oneExceptionalOrbit J exceptional
    (c1DegreeNineSource_local_capacity_without_catalogue hChief hgen hindex published8 h18 J exceptional
      hexceptional hunique hnoA4)

end SymmetricSubgroupAsymptotics
