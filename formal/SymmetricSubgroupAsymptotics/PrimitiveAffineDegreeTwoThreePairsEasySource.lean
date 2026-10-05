import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixSmallComparators
import SymmetricSubgroupAsymptotics.Non2PreE7AbstractS4Source
import SymmetricSubgroupAsymptotics.NaturalA4ScalarFourHead
import SymmetricSubgroupAsymptotics.NaturalA4ComparatorAction

/-!
# The five small-comparator rows in the three-pair slice

The published transitive degree-six catalogue gives eight nonbinary actions
with a system of three pairs.  Five abstract targets already have faithful
actions on fewer than six points:

* `C3 × C2` on `3 + 2` points;
* `A4` on four points;
* regular `S3` on three points;
* `S3 × C2` on `3 + 2` points; and
* either of the two degree-six actions of the abstract group `S4`, using its
  natural four-point action as comparator.

This file packages precisely those five rows in the concrete source interface
used by the affine exceptional-cell dispatcher.  The two central products
`A4 × C2` and `S4 × C2` are deliberately absent: their equal-width actions
need the joint central-repeat estimate rather than a self-comparator.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

private abbrev C2 := Multiplicative (ZMod 2)
private abbrev C3 := CyclicThree
private abbrev A4 := NaturalA4ScalarFourHead.G

/-- The faithful disjoint action of `C3 × C2` on five labelled points. -/
def cyclicSixComparatorAction : C3 × C2 →* Equiv.Perm (Fin 5) :=
  s3c2Action.comp
    (NaturalA4RankTail.comparatorAction.prodMap (MonoidHom.id C2))

theorem cyclicSixComparatorAction_injective :
    Function.Injective cyclicSixComparatorAction := by
  intro x y hxy
  have hprod :
      (NaturalA4RankTail.comparatorAction x.1, x.2) =
        (NaturalA4RankTail.comparatorAction y.1, y.2) :=
    s3c2Action_injective hxy
  apply Prod.ext
  · exact NaturalA4RankTail.comparatorAction_injective
      (congrArg Prod.fst hprod)
  · exact congrArg
      (fun z : Equiv.Perm (Fin 3) × C2 => z.2) hprod

/-- The five three-pair abstract groups whose complete source is supplied by
an already checked smaller faithful comparator.  Both degree-six `S4`
permutation representations use the same final constructor because the
source theorem depends only on the abstract group. -/
inductive PublishedThreePairEasyModel
    (U : PreE7NonPairActionClass 6) : Type
  | cyclicSix
      (equiv : preE7NonPairAction 6 U ≃* C3 × C2)
  | alternatingFour
      (equiv : preE7NonPairAction 6 U ≃* A4)
  | symmetricThree
      (equiv : preE7NonPairAction 6 U ≃* Equiv.Perm (Fin 3))
  | symmetricThreeTimesTwo
      (equiv : preE7NonPairAction 6 U ≃* Equiv.Perm (Fin 3) × C2)
  | abstractSymmetricFour
      (equiv : preE7NonPairAction 6 U ≃* Equiv.Perm (Fin 4))

namespace PublishedThreePairEasyModel

/-- Every easy row enters the exact source-or-Yoneda-top interface. -/
noncomputable def source
    {U : PreE7NonPairActionClass 6}
    (M : PublishedThreePairEasyModel U) :
    PreE7RankTailSourceOrYonedaTopData 6 U :=
  match M with
  | .cyclicSix e =>
      DegreeSixSelfComparatorSource.source U 5 (by norm_num) (by norm_num)
        (cyclicSixComparatorAction.comp e.toMonoidHom)
        (cyclicSixComparatorAction_injective.comp e.injective)
  | .alternatingFour e =>
      DegreeSixSelfComparatorSource.source U 4 (by norm_num) (by norm_num)
        (A4.subtype.comp e.toMonoidHom)
        (Subtype.val_injective.comp e.injective)
  | .symmetricThree e =>
      (PreE7DegreeSixS3Source.mk e).source
  | .symmetricThreeTimesTwo e =>
      (PreE7DegreeSixS3C2Source.mk e).source
  | .abstractSymmetricFour e =>
      .inl ((PreE7AbstractS4Source.mk e).toRankTailOwnerSource)

end PublishedThreePairEasyModel

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
