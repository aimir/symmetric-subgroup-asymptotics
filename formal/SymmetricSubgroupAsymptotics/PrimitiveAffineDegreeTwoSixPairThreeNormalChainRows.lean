import SymmetricSubgroupAsymptotics.FiniteThreeNormalChainQuotientRows
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairLiteralOneGeneralRows

/-!
# Three-normal-chain rows for the six-pair catalogue

This is the variable normal-state adapter for selected six-pair actions with
a checked normal lattice `⊥ < E < ⊤`.  It applies the generic chain
quotient constructor to every state in the action's surjective normal
registry.  The normal count and registry order remain those of the literal
action, so an emitter does not need a parallel row table or a `fin_cases`
assembly.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- A checked literal six-pair action whose complete normal lattice is a
three-point chain. -/
structure PrimitiveAffineDegreeTwoSixPairThreeNormalChainFiniteRowData where
  literal : PrimitiveAffineDegreeTwoSixPairCheckedLiteralAction
  chain : FiniteThreeNormalChainData literal.G

namespace PrimitiveAffineDegreeTwoSixPairThreeNormalChainFiniteRowData

variable
  (D : PrimitiveAffineDegreeTwoSixPairThreeNormalChainFiniteRowData)

/-- Construct all registry-indexed one-general rows directly from the
exhaustive normal-chain datum. -/
noncomputable def toOneGeneralFiniteRowData :
    PrimitiveAffineDegreeTwoSixPairLiteralOneGeneralFiniteRowData where
  literal := D.literal
  socleGenerator i := by
    exact D.chain.quotientSocleGenerator
      (D.literal.normalStateIndex i).1

/-- Package the variable state rows as literal quotient certificates. -/
noncomputable def toCheckedLiteralQuotientAction
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PrimitiveAffineDegreeTwoSixPairCheckedLiteralQuotientAction :=
  D.toOneGeneralFiniteRowData.toCheckedLiteralQuotientAction hZmud

/-- Assemble the complete B6 action certificate on the same literal action. -/
noncomputable def toB6ActionCertificate
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7B6ActionCertificate D.literal.G :=
  D.toOneGeneralFiniteRowData.toB6ActionCertificate hZmud

end PrimitiveAffineDegreeTwoSixPairThreeNormalChainFiniteRowData

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
