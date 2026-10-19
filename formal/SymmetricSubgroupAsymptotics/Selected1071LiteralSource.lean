import SymmetricSubgroupAsymptotics.Selected1071LiteralActionClass
import SymmetricSubgroupAsymptotics.Selected1071SourceOfEquivalence

/-! The selected literal action class has a complete original-normal
source. Its placement into a 527-entry table is a separate locator task. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1071QuotientGraph
open Non2UnipotentPrefixFiniteMenu

def literalSource (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    PreE7RankTailSourceOrYonedaTopData 16 literalRepresentative :=
  sourceOfEquivalence literalRepresentative literalRepresentativeEquiv hZmud lit

end SymmetricSubgroupAsymptotics.Selected1071QuotientGraph
