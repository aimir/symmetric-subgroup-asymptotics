import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenCanonicalCatalogue
import SymmetricSubgroupAsymptotics.SixteenPointNonPairOriginalChart

/-! The primitive constructor of the original sixteen-point reduction.
The only classification boundary is the fixed twenty-two-action canonical
catalogue. All twenty-two original normal and local representation bounds
are supplied by the checked literal frame family, including A16 and S16.
No local-quotient eligibility exclusions or finite frame assumptions remain
in this constructor. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Compose the retained original point chart with the exact canonical
catalogue conjugacy. The original permutation action is not replaced by
an abstractly isomorphic group. -/
def SixteenPointNonPairOriginalChart.primitiveLiteralMatch
    {X : Type} {S : Subgroup (Equiv.Perm X)}
    (C : SixteenPointNonPairOriginalChart S)
    (published : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (hprimitive : MulAction.IsPreprimitive (preE7NonPairAction 16 C.index) (Fin 16)) :
    PrimitiveAffineSixteenAllLiteralFrames.LiteralMatch S := by
  let selected := PrimitiveSixteenCanonicalCatalogue.originalClassification
    published (preE7NonPairAction 16 C.index) hprimitive
  let j := Classical.choose selected
  let selectedConjugator := Classical.choose_spec selected
  let g := Classical.choose selectedConjugator
  refine {
    index := j
    points := C.points
    conjugator := g
    matched := ?_ }
  rw [C.matched]
  exact Classical.choose_spec selectedConjugator

namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

/-- Close the actual primitive-sixteen branch of the original degree-four
frame problem. The bound is the internal sum 2 + 8 ≤ 10. -/
def degreeFourZeroCoreSixteenPrimitiveBounds
    (published : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (C : SixteenPointNonPairOriginalChart block.Top)
    (hprimitive : MulAction.IsPreprimitive (preE7NonPairAction 16 C.index) (Fin 16)) :
    DegreeFourZeroCoreFiniteFrameBounds block P 10 :=
  degreeFourZeroCoreSixteenPrimitiveLiteralBounds block P hr hD
    (C.primitiveLiteralMatch published hprimitive)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
