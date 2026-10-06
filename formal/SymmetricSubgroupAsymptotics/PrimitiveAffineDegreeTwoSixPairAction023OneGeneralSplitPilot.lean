import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction023OneGeneralBottomRow
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction023OneGeneralMiddleRow
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction023OneGeneralTopRow
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairLiteralOneGeneralRows
import Mathlib.Tactic.FinCases

/-!
# Selected six-pair action 023: split one-general assembly

The finite middle table, normal-chain proof, and three quotient witnesses are
checked in separate modules.  This final module only assembles those opaque
rows into the common literal character and B6 interfaces.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoSixPairAction023OneGeneralSplit

open Non2UnipotentPrefixFiniteMenu

noncomputable def degreeTwoSixPairAction023SplitOneGeneralFiniteRowData :
    PrimitiveAffineDegreeTwoSixPairLiteralOneGeneralFiniteRowData where
  literal := degreeTwoSixPairAction023CheckedLiteral
  socleGenerator i := by
    fin_cases i
    · simpa [stateZero] using stateZeroSocleGenerator
    · simpa [stateMiddle] using stateMiddleSocleGenerator
    · simpa [stateTop] using stateTopSocleGenerator

noncomputable def degreeTwoSixPairAction023SplitCheckedLiteralQuotientAction
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PrimitiveAffineDegreeTwoSixPairCheckedLiteralQuotientAction :=
  degreeTwoSixPairAction023SplitOneGeneralFiniteRowData
    |>.toCheckedLiteralQuotientAction hZmud

noncomputable def degreeTwoSixPairAction023SplitB6ActionCertificate
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7B6ActionCertificate degreeTwoSixPairAction023CheckedLiteral.G :=
  degreeTwoSixPairAction023SplitOneGeneralFiniteRowData
    |>.toB6ActionCertificate hZmud

end PrimitiveAffineDegreeTwoSixPairAction023OneGeneralSplit
end SymmetricSubgroupAsymptotics

end
