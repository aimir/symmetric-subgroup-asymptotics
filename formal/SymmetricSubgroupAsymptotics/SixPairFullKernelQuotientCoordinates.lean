import SymmetricSubgroupAsymptotics.SixPairCoarseWreathHeadKernel
import SymmetricSubgroupAsymptotics.TwoBinaryThreeWreathCoordinates
import SymmetricSubgroupAsymptotics.ScalarFourCentralCoordinatePullback

/-! The SAME actual original center quotient receives two central bits
and two scalar planes through its faithful physical head embedding.
Neither the original quotient nor its physical factors are assigned a
new transitive action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairFullKernelQuotientCoordinates
open SixPairFullKernelCenter SixPairCoarseWreathHeadKernel

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))
  (hfull : SixPairIndependentKernelNormalCommutators.Independent F E)
  (hrotation : OddMarkerTernaryChart.rotation∈
    (SixPairNestedTopFrames.nestedFrame F E).top.range)

theorem retained_top_surjective : Function.Surjective
    ((TwoBinaryThreeWreathCoordinates.coordinates
      (SixPairNestedTopFrames.nestedFrame F E).top.range hrotation).top.comp
      (quotientHead F E hfull)) := by
  intro t
  obtain ⟨u,hu⟩ := (SixPairNestedTopFrames.nestedFrame F E).top.rangeRestrict_surjective t
  refine ⟨QuotientGroup.mk' (centerImage F E) u,?_⟩
  change (SixPairNestedTopFrames.nestedFrame F E).top.rangeRestrict u=t
  exact hu

/-- Actual full-independent geometry supplies the rank-two structural
packet required by the all-original-normal source theorem. -/
def coordinates : ScalarFourCentralTopCoordinates
    (U ⧸ centerImage F E)
    (SixPairNestedTopFrames.nestedFrame F E).top.range 2 2 :=
  (TwoBinaryThreeWreathCoordinates.coordinates
    (SixPairNestedTopFrames.nestedFrame F E).top.range hrotation).ofInjective
      (quotientHead F E hfull) (quotientHead_injective F E hfull)
      (retained_top_surjective F E hfull hrotation)

end SymmetricSubgroupAsymptotics.SixPairFullKernelQuotientCoordinates
