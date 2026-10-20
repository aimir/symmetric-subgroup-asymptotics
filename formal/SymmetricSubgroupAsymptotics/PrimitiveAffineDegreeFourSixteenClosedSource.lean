import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourSixteenZeroInnerBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourSixteenPrimitiveSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourEightClosedSource

/-! Every original sixteen-block zero-core frame is discharged by the
exhaustive structural reduction. No finite-frame callback remains. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)

def degreeFourZeroCoreSixteenBounds_of_published
    {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre) [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre=4) (hD : degreeFourTernaryCore block P=⊥)
    (hs : Nat.card block.Points=16) : DegreeFourZeroCoreFiniteFrameBounds block P 10 := by
  cases degreeFourSixteenFrameReduction block P published8 socle hMN hClifford
      hTraceyPerm hr hD hs with
  | bounded B => exact B
  | pair F hker M eligible =>
      exact degreeFourZeroCoreSixteenPairKernelNontrivialBounds_of_canonical
        block P published8 hr hD F hker (by simp)
  | primitive C hp =>
      exact degreeFourZeroCoreSixteenPrimitiveBounds block P published16 hr hD C hp
  | zero C b inner R hi hsInner hzero =>
      exact degreeFourZeroCoreSixteenZeroInnerBounds block P hMN hr hD C inner R hi hsInner hzero

def degreeFourZeroCoreSixteenFrameBounds_of_published : DegreeFourZeroCoreSixteenFrameBoundsInput := by
  intro w U basePoint block P _ hr hD hs
  exact degreeFourZeroCoreSixteenBounds_of_published published8 published16 socle hMN hClifford hTraceyPerm block P hr hD hs

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
