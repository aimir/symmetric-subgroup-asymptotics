import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairNormalStateQuotients
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairCharacterOnlySource

/-!
# Literal character rows for the six-pair catalogue

The character-only source theorem supplies two compact quotient shapes:
one Zmud general position, or one literal linear position together with one
inflated Zmud general position.  The finite six-pair emitter should record
one of those shapes only for each checked normal-registry state.

This file converts that finite state family to the common quotient-certificate
family.  The checked normal-state dispatcher then installs the result on
every arbitrary literal normal quotient.  The construction stays on the
same physical twelve-point action; the separate published catalogue
correspondence is not used here.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

namespace PreE7B6CharacterAxisData

variable {Q : Type} [Group Q] [Finite Q]
  (A : PreE7B6CharacterAxisData Q)

/-- Turn either finite character-axis shape into the quotient constructor
consumed by B6.  The common profile theorem supplies the cold slope. -/
noncomputable def toB6QuotientCertificate
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7B6QuotientCertificate Q :=
  .character (A.certificate hZmud)
    (CharacterQuotientCertificate.slope_le_four_thirds_of_mixed
      (A.certificate hZmud)
      (A.certificate_mixed hZmud)
      (A.certificate_noBinary hZmud)
      (A.certificate_profile hZmud))

end PreE7B6CharacterAxisData

/-- One compact character-axis choice on every emitted normal-registry
state of the same literal action. -/
abbrev PrimitiveAffineDegreeTwoSixPairLiteralCharacterAxisStateFamily
    (D : PrimitiveAffineDegreeTwoSixPairCheckedLiteralAction) :=
  PrimitiveAffineDegreeTwoSixPairNormalStateFamily D
    (fun N => PreE7B6CharacterAxisData (D.G ⧸ N.1))

namespace PrimitiveAffineDegreeTwoSixPairLiteralCharacterAxisStateFamily

variable {D : PrimitiveAffineDegreeTwoSixPairCheckedLiteralAction}
  (F : PrimitiveAffineDegreeTwoSixPairLiteralCharacterAxisStateFamily D)

/-- Convert the finite character-axis rows pointwise.  The resulting family
is still indexed only by checked registry states; arbitrary-normal dispatch
is performed by the common quotient layer. -/
noncomputable def toQuotientCertificateStateFamily
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PrimitiveAffineDegreeTwoSixPairQuotientCertificateStateFamily D :=
  PrimitiveAffineDegreeTwoSixPairNormalStateFamily.map F
    (fun _ A => A.toB6QuotientCertificate hZmud)

end PrimitiveAffineDegreeTwoSixPairLiteralCharacterAxisStateFamily

/-- The exact source-only payload for one character-only literal catalogue
action.  Varying action, class, normal, and generator counts remain packaged
inside `literal`; the emitter supplies only one finite axis row per checked
normal state. -/
structure PrimitiveAffineDegreeTwoSixPairLiteralCharacterFiniteRowData where
  literal : PrimitiveAffineDegreeTwoSixPairCheckedLiteralAction
  axes : PrimitiveAffineDegreeTwoSixPairLiteralCharacterAxisStateFamily literal

namespace PrimitiveAffineDegreeTwoSixPairLiteralCharacterFiniteRowData

variable (D : PrimitiveAffineDegreeTwoSixPairLiteralCharacterFiniteRowData)

/-- Package the literal structural witness and its converted quotient rows. -/
noncomputable def toCheckedLiteralQuotientAction
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PrimitiveAffineDegreeTwoSixPairCheckedLiteralQuotientAction where
  literal := D.literal
  certificates := D.axes.toQuotientCertificateStateFamily hZmud

/-- Assemble the complete B6 certificate on the same literal action. -/
noncomputable def toB6ActionCertificate
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7B6ActionCertificate D.literal.G :=
  (D.toCheckedLiteralQuotientAction hZmud).toB6ActionCertificate

end PrimitiveAffineDegreeTwoSixPairLiteralCharacterFiniteRowData

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
