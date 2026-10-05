import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixBlockSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixS3ProductAlgebra
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixThreeSquaredC4Source
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixS3WreathAlgebra
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixSmallComparators

/-!
# The published three-by-two affine slice in degree six

Butler--McKay's published classification of transitive groups of degree six
has four rows whose minimal blocks have size three, exact affine component
`S₃`, and nontrivial block-kernel sign image.  Their abstract groups are

* `S₃ × C₂` (`6T3`),
* `S₃ × S₃` (`6T9`),
* `3² : C₄` (`6T10`), and
* `S₃ ≀ C₂` (`6T13`).

This file states only that finite published correspondence.  All counting
estimates for the four rows, and the complete source for the complementary
trivial-sign branch, are proved in Lean in the imported modules.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

private abbrev C2 := Multiplicative (ZMod 2)

/-- The four literal group models in the nontrivial-sign three-by-two slice
of the published transitive degree-six catalogue. -/
inductive PublishedDegreeSixThreeByTwoAffineModel
    (U : PreE7NonPairActionClass 6) : Type
  | s3c2
      (equiv : preE7NonPairAction 6 U ≃*
        Equiv.Perm (Fin 3) × C2)
  | s3Product
      (data : PreE7DegreeSixS3ProductSource U)
  | threeSquaredC4
      (data : PreE7DegreeSixThreeSquaredC4Source U)
  | s3Wreath
      (data : PreE7DegreeSixS3WreathSource U)

/-- **Published finite classification input.**  This is the four-row
three-by-two affine slice of Butler--McKay's transitive degree-six list,
with the actual group identification retained in precisely the form used by
the four checked Lean consumers. -/
def PublishedDegreeSixThreeByTwoAffineClassification : Prop :=
  ∀ (U : PreE7NonPairActionClass 6) (basePoint : Fin 6)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction 6 U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre),
    Nat.card block.Fibre = 3 → Nat.card block.Points = 2 →
    DegreeThreeBlockInversionHead.coordinateSigns
        block.map block.map_equivariant ≠ 1 →
      Nonempty (PublishedDegreeSixThreeByTwoAffineModel U)

namespace PublishedDegreeSixThreeByTwoAffineModel

/-- Every one of the four published rows has a completed source.  No
classification or asymptotic estimate is hidden in this dispatch. -/
noncomputable def source
    {U : PreE7NonPairActionClass 6}
    (M : PublishedDegreeSixThreeByTwoAffineModel U) :
    PreE7RankTailSourceOrYonedaTopData 6 U :=
  match M with
  | .s3c2 e => (PreE7DegreeSixS3C2Source.mk e).source
  | .s3Product S => S.source DegreeSixS3Product.algebra
  | .threeSquaredC4 S => S.source
  | .s3Wreath S => S.source DegreeSixS3Wreath.algebra

end PublishedDegreeSixThreeByTwoAffineModel

namespace PrimitiveAffineImprimitiveBlockTransfer

/-- The published four-row list plus the already proved trivial-sign owner
closes every actual three-by-two affine block cell. -/
noncomputable def degreeSixSource_of_publishedClassification
    (hKP : KovacsPraegerAbelianizationBound)
    (classification : PublishedDegreeSixThreeByTwoAffineClassification)
    (U : PreE7NonPairActionClass 6) (basePoint : Fin 6)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction 6 U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hFibre : Nat.card block.Fibre = 3)
    (hPoints : Nat.card block.Points = 2) :
    PreE7RankTailSourceOrYonedaTopData 6 U := by
  by_cases hSigns : DegreeThreeBlockInversionHead.coordinateSigns
      block.map block.map_equivariant = 1
  · exact degreeSixSource_of_three_by_two_trivialSigns
      block P hKP hFibre hPoints hSigns
  · exact (Classical.choice
      (classification U basePoint block P hFibre hPoints hSigns)).source

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
