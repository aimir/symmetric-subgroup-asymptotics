import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixBlockSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixS3ProductAlgebra
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixThreeSquaredC4Source
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixS3WreathAlgebra

/-!
# The degree-six zero-head dispatcher

The three concrete normal-comparator sources for the zero-head three-by-two
cell have the same output.  This file packages their exact recognition data
as a disjoint sum and dispatches each recognized literal group to that output.

No completeness assertion is made here.  After the block theorem has reduced
the low branch to vanishing of every normal ternary relative head, the one
remaining finite-group input is a construction of
`PreE7DegreeSixZeroHeadRecognition U`.  Keeping that input explicit prevents
the dispatcher from silently assuming that the three models exhaust the
literal affine cell.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The low-branch conclusion already supplied by the three-by-two block
theorem: every normal ternary relative-character head vanishes. -/
abbrev PreE7DegreeSixAllNormalTernaryHeadsZero
    (U : PreE7NonPairActionClass 6) : Prop :=
  ∀ (N : Subgroup (preE7NonPairAction 6 U)) [N.Normal],
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 0

/-- Exact recognition data accepted by the zero-head dispatcher.  Each case
retains precisely the literal equivalence (and, in the affine case, the
literal irreducible complement) required by its existing source module. -/
inductive PreE7DegreeSixZeroHeadRecognition
    (U : PreE7NonPairActionClass 6) : Type
  | s3Product (data : PreE7DegreeSixS3ProductSource U)
  | threeSquaredC4 (data : PreE7DegreeSixThreeSquaredC4Source U)
  | s3Wreath (data : PreE7DegreeSixS3WreathSource U)

/-- The smallest outstanding cell-specific input after all normal ternary
heads have been proved zero.  A finite classifier may close over the literal
block and its affine profile when constructing this function. -/
abbrev PreE7DegreeSixZeroHeadRecognizer
    (U : PreE7NonPairActionClass 6) : Type :=
  PreE7DegreeSixAllNormalTernaryHeadsZero U →
    PreE7DegreeSixZeroHeadRecognition U

namespace PreE7DegreeSixZeroHeadRecognition

variable {U : PreE7NonPairActionClass 6}

/-- Dispatch a recognized zero-head group through its completed concrete
normal-comparator source. -/
noncomputable def source
    (R : PreE7DegreeSixZeroHeadRecognition U) :
    PreE7RankTailSourceOrYonedaTopData 6 U :=
  match R with
  | .s3Product S =>
      S.source DegreeSixS3Product.algebra
  | .threeSquaredC4 S =>
      S.source
  | .s3Wreath S =>
      S.source DegreeSixS3Wreath.algebra

end PreE7DegreeSixZeroHeadRecognition

namespace PrimitiveAffineImprimitiveBlockTransfer

variable {U : PreE7NonPairActionClass 6}
  {basePoint : Fin 6}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction 6 U) basePoint)

/-- Bridge from the literal three-by-two block dichotomy to the zero-head
dispatcher.  The existing block theorem proves the zero-head premise; only
the finite recognition function remains an input. -/
noncomputable def degreeSixZeroHeadSource_of_three_by_two_no_high
    (hFibre : Nat.card block.Fibre = 3)
    (hPoints : Nat.card block.Points = 2)
    (hNoHigh : ∀ (N : Subgroup (preE7NonPairAction 6 U)) [N.Normal],
      ¬ 3 * 6 <
        20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N))
    (recognize : PreE7DegreeSixZeroHeadRecognizer U) :
    PreE7RankTailSourceOrYonedaTopData 6 U :=
  (recognize
    (all_normal_head_zero_of_no_three_by_two_high
      block hFibre hPoints hNoHigh)).source

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
