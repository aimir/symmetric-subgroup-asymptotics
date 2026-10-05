import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoCentralProductNumerics
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveDegreeTwoOwnerReduction

/-!
# The published three-pair affine slice

The transitive degree-six catalogue has five smaller-comparator abstract
groups and the two central-product abstract groups.  The two degree-six
permutation representations of `S4` share one abstract-group constructor,
so this seven-model list covers the eight literal action rows.

The input below is only the Butler--McKay finite correspondence.  Every
source estimate attached to a model is proved in the imported Lean files.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Abstract group model for a literal retained action with three blocks of
size two. -/
inductive PublishedDegreeTwoThreePairModel
    (U : PreE7NonPairActionClass 6) : Type
  | easy (model : PublishedThreePairEasyModel U)
  | central (model : PublishedThreePairCentralModel U)

namespace PublishedDegreeTwoThreePairModel

noncomputable def source
    {U : PreE7NonPairActionClass 6}
    (M : PublishedDegreeTwoThreePairModel U) :
    PreE7RankTailSourceOrYonedaTopData 6 U :=
  match M with
  | .easy model => model.source
  | .central model => model.rankTailSource

end PublishedDegreeTwoThreePairModel

/-- **Published finite correspondence.**  This is the three-pair slice of
the Butler--McKay transitive degree-six list, retaining the actual abstract
group isomorphism used by the checked source theorem. -/
def PublishedDegreeTwoThreePairClassification : Prop :=
  ∀ (U : PreE7NonPairActionClass 6) (basePoint : Fin 6)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction 6 U) basePoint),
    Nat.card block.Fibre = 2 → Nat.card block.Points = 3 →
      Nonempty (PublishedDegreeTwoThreePairModel U)

namespace PrimitiveAffineImprimitiveBlockTransfer

/-- Dispatch the three-pair cell through the exact published model list. -/
noncomputable def degreeTwoThreePairSource
    (classification : PublishedDegreeTwoThreePairClassification)
    (U : PreE7NonPairActionClass 6) (basePoint : Fin 6)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction 6 U) basePoint)
    (hFibre : Nat.card block.Fibre = 2)
    (hPoints : Nat.card block.Points = 3) :
    PreE7RankTailSourceOrYonedaTopData 6 U :=
  (Classical.choice
    (classification U basePoint block hFibre hPoints)).source

end PrimitiveAffineImprimitiveBlockTransfer

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
