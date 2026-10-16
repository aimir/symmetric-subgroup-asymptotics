import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourEightCompleteHeadSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreResidualAssembly

/-! The complete original eight-block frame input, obtained from the
fixed published catalogue and the checked original local head bounds. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

def degreeFourZeroCoreEightBounds_of_canonical
    (published : DegreeEightCanonicalCatalogue.PublishedClassification)
    {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (hs : Nat.card block.Points = 8) :
    DegreeFourZeroCoreFiniteFrameBounds block P 5 := by
  letI : MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive
  let M := DegreeEightCanonicalCatalogue.transitiveLiteralMatch published block.Top hs
    (degreeFourZeroCoreTop_not_isPGroup_two block P hr hD)
  exact degreeFourZeroCoreEightBounds_of_match block P hr hD M

/-- No project-owned matching, finite-frame or numerical premise remains
in the eight-block callback. -/
def degreeFourZeroCoreEightFrameBounds_of_published
    (published : DegreeEightCanonicalCatalogue.PublishedClassification) :
    DegreeFourZeroCoreEightFrameBoundsInput := by
  intro w U basePoint block P _ hr hD hs
  exact degreeFourZeroCoreEightBounds_of_canonical published block P hr hD hs

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
