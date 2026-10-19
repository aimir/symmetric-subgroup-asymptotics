import SymmetricSubgroupAsymptotics.Selected1071ActualCentralRepeat
import SymmetricSubgroupAsymptotics.ScalarFourCentralCoordinatesTransport
import SymmetricSubgroupAsymptotics.ScalarFourCentralCubicActualSource
import SymmetricSubgroupAsymptotics.CyclicThreeRegularPermutation

/-! The selected source consumes an actual original group equivalence.
No semantic locator or indexed coverage is inferred from a row label. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1071QuotientGraph
open Non2UnipotentPrefixFiniteMenu

 def sourceOfEquivalence (U : PreE7NonPairActionClass 16)
    (e : preE7NonPairAction 16 U ≃* Original)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    PreE7RankTailSourceOrYonedaTopData 16 U :=
  (actualCentralRepeat.transport e).cubicActualSource (by decide) (by decide) rfl
    CyclicThreeRegularPermutation.representation
    CyclicThreeRegularPermutation.representation_injective hZmud lit

end SymmetricSubgroupAsymptotics.Selected1071QuotientGraph
