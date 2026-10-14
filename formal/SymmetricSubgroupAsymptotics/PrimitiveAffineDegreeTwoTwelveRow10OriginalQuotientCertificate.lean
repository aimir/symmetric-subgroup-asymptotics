import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveExceptionalOriginalQuotients
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow10ExceptionalAssembly

/-! # Row 10 in the corrected exceptional original-quotient interface -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow10OriginalQuotientCertificate

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelveExceptionalOriginalQuotients
open PrimitiveAffineDegreeTwoTwelveRow10ExceptionalAssembly
open PrimitiveAffineDegreeTwoTwelveRow10OriginalGeometry

/-- Row 10 supplies every actual original quotient anchor. No scalar
`topSocle = 1` certificate or new group-theoretic premise is requested. -/
def certificate : RowCertificate rowInterface :=
  RowCertificate.ofSymmetricThreeCore
    (fun _hZmud _p R N hbinaryTop ↦
      (Classical.choice
        (PrimitiveAffineDegreeTwoTwelveRow10NormalizerPrefix.binary_top_quotient_orbitInput
          R N hbinaryTop)).anchor)
    (fun hZmud _p R N hnonbinaryTop ↦ by
      letI : N.1.Normal := N.2
      apply nonbinary_quotient_anchor R hZmud N
      intro hQ
      exact hnonbinaryTop
        (hQ.of_surjective (R.quotientMap N) (R.quotientMap_surjective N)))

/-- The corrected interface recovers the complete row payload with its
existing numerical menu. -/
def resolvedData (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization rowInterface p) :
    DegreeTwoPairTopRelativeResolvedData rowInterface degreeTwoTwelvePairExceptionalProfiles p :=
  certificate.resolvedData hZmud lit R

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow10OriginalQuotientCertificate

end
