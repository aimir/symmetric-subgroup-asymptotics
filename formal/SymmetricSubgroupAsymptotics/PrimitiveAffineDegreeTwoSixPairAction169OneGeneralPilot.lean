import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169NormalChain
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairThreeNormalChainRows

/-!
# Selected six-pair action 169: variable-state one-general pilot

The action-specific source ends at the checked three-normal-chain datum.
The common variable-state assembler supplies every literal quotient row.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ThreeNormalChain

open Non2UnipotentPrefixFiniteMenu

noncomputable def degreeTwoSixPairAction169ThreeNormalChainFiniteRowData :
    PrimitiveAffineDegreeTwoSixPairThreeNormalChainFiniteRowData where
  literal := degreeTwoSixPairAction169CheckedLiteral
  chain := chainData

noncomputable def degreeTwoSixPairAction169OneGeneralFiniteRowData :
    PrimitiveAffineDegreeTwoSixPairLiteralOneGeneralFiniteRowData :=
  degreeTwoSixPairAction169ThreeNormalChainFiniteRowData
    |>.toOneGeneralFiniteRowData

noncomputable def degreeTwoSixPairAction169CheckedLiteralQuotientAction
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PrimitiveAffineDegreeTwoSixPairCheckedLiteralQuotientAction :=
  degreeTwoSixPairAction169ThreeNormalChainFiniteRowData
    |>.toCheckedLiteralQuotientAction hZmud

noncomputable def degreeTwoSixPairAction169B6ActionCertificate
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7B6ActionCertificate degreeTwoSixPairAction169CheckedLiteral.G :=
  degreeTwoSixPairAction169ThreeNormalChainFiniteRowData
    |>.toB6ActionCertificate hZmud

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ThreeNormalChain

end
