import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairLiteralCharacterRows

/-!
# One-general literal rows for the six-pair catalogue

Most character-only six-pair quotient rows need just one normally generating
socle element.  This file gives the narrow finite consumer for that common
case.  An emitter supplies one `SocleNormalGeneratorBound` for each checked
normal-registry state of the literal action.  The generic normal-state
dispatcher and the published Zmud input perform all later assembly.

The first finite pilot for this interface is selected action 147.  It has
only two checked normal states, so that pilot can test the bottom quotient
and the trivial top quotient before any broader quotient-row emission.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The exact finite input for a literal action whose every quotient uses
one general character position.  The field is indexed by the checked normal
registry, never by an independently asserted normal list. -/
structure PrimitiveAffineDegreeTwoSixPairLiteralOneGeneralFiniteRowData where
  literal : PrimitiveAffineDegreeTwoSixPairCheckedLiteralAction
  socleGenerator : ∀ i : Fin literal.normalCount,
    SocleNormalGeneratorBound
      (literal.G ⧸ (literal.normalStateIndex i).1) 1

namespace PrimitiveAffineDegreeTwoSixPairLiteralOneGeneralFiniteRowData

variable (D : PrimitiveAffineDegreeTwoSixPairLiteralOneGeneralFiniteRowData)

/-- Regard each checked one-generator witness as the corresponding compact
character-axis alternative. -/
def toCharacterAxisStateFamily :
    PrimitiveAffineDegreeTwoSixPairLiteralCharacterAxisStateFamily D.literal where
  state i := .oneGeneral (D.socleGenerator i)

/-- Package the finite state rows for the common literal character adapter. -/
def toLiteralCharacterFiniteRowData :
    PrimitiveAffineDegreeTwoSixPairLiteralCharacterFiniteRowData where
  literal := D.literal
  axes := D.toCharacterAxisStateFamily

/-- Convert all finite one-general rows to literal quotient certificates. -/
noncomputable def toCheckedLiteralQuotientAction
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PrimitiveAffineDegreeTwoSixPairCheckedLiteralQuotientAction :=
  D.toLiteralCharacterFiniteRowData.toCheckedLiteralQuotientAction hZmud

/-- Assemble the complete B6 certificate on the same literal action. -/
noncomputable def toB6ActionCertificate
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7B6ActionCertificate D.literal.G :=
  D.toLiteralCharacterFiniteRowData.toB6ActionCertificate hZmud

end PrimitiveAffineDegreeTwoSixPairLiteralOneGeneralFiniteRowData

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
