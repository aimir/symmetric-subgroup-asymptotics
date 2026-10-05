import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction001Witness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairCatalogueDispatcher

/-!
# Six-pair catalogue row 1: checked literal action

This adapter places the completed action-1 physical witness in the common
182-row catalogue schema.  Quotient certificates and the published
degree-twelve locator are intentionally separate later layers.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The completed structural part of selected catalogue action 1. -/
noncomputable def degreeTwoSixPairAction001CheckedLiteral :
    PrimitiveAffineDegreeTwoSixPairCheckedLiteralAction where
  G := PrimitiveAffineDegreeTwoSixPairAction001Witness.Original
  ambientCount := 3
  classCount := 6
  normalCount := 7
  normalGeneratorWidth := 3
  ambient := PrimitiveAffineDegreeTwoSixPairAction001Witness.ambient
  representative := PrimitiveAffineDegreeTwoSixPairAction001Witness.representative
  stateGenerators := PrimitiveAffineDegreeTwoSixPairAction001Witness.stateGenerators
  checked := PrimitiveAffineDegreeTwoSixPairAction001Witness.selectedWitness

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
