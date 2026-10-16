import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourSixteenStructuralReduction
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourSixteenPrimitiveSource

/-! Close the primitive constructor of the actual sixteen-point
structural dispatcher. The remaining geometric constructors retain only
the eligible eight-point pair frame and zero-ternary four-by-four action. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

inductive DegreeFourSixteenPrimitiveClosedReduction : Type 1 where
  | bounded (bound : DegreeFourZeroCoreFiniteFrameBounds block P 10)
  | pair (frame : BinaryPairFrame block.Top (Fin 8))
      (nontrivialKernel : frame.top.ker ≠ ⊥)
      (literal : DegreeEightCanonicalCatalogue.TransitiveLiteralMatch frame.top.range)
      (eligible : ¬ DegreeFourEightTopEligibility.Excluded literal.index)
  | zero (chart : SixteenPointNonPairOriginalChart block.Top) (b : Fin 16)
      (inner : OriginalMinimalBlock (A := preE7NonPairAction 16 chart.index) b)
      [Nontrivial inner.Fibre]
      (profile : PrimitiveAffineProfile inner.Component inner.Fibre)
      (fibre : Nat.card inner.Fibre = 4) (points : Nat.card inner.Points = 4)
      (zeroCore : degreeFourTernaryCore inner profile = ⊥)

def DegreeFourSixteenFrameReduction.closePrimitive
    (published : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (R : DegreeFourSixteenFrameReduction block P) :
    DegreeFourSixteenPrimitiveClosedReduction block P := by
  cases R with
  | bounded bound => exact .bounded bound
  | pair frame hker literal eligible => exact .pair frame hker literal eligible
  | primitive chart hprimitive =>
      exact .bounded (degreeFourZeroCoreSixteenPrimitiveBounds block P
        published hr hD chart hprimitive)
  | @zero chart b inner hnontrivial profile fibre points zeroCore =>
      letI : Nontrivial inner.Fibre := hnontrivial
      exact .zero chart b inner profile fibre points zeroCore

/-- Exact fixed canonical classification inputs remain explicit. No
numerical frame bound or project coverage premise is introduced. -/
def degreeFourSixteenPrimitiveClosedReduction
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (hTracey : TraceySolubleOrbitInducedModuleInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (hs : Nat.card block.Points = 16) :
    DegreeFourSixteenPrimitiveClosedReduction block P :=
  DegreeFourSixteenFrameReduction.closePrimitive block P published16 hr hD
    (degreeFourSixteenFrameReduction block P published8 socle
      hTracey hMN hClifford hTraceyPerm hr hD hs)

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
