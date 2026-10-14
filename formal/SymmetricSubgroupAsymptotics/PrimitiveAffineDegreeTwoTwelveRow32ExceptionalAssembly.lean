import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow32OriginalSocle
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveExceptionalOriginalQuotients

/-!
# Original-quotient exceptional data for literal row 32

The existing top-normal state selects the binary normalizer prefix or the
proved ternary whole-socle anchor. Both profiles belong to the existing
exceptional numerical menu. Every anchor retains the original normal
quotient, and the literal module proof supplies the nonbinary branch.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow32ExceptionalAssembly

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelveExceptionalOriginalQuotients

abbrev rowInterface := DegreeTwoTwelvePairFiniteCatalogue.row32Interface

def certificate : RowCertificate rowInterface := by
  refine RowCertificate.ofBinaryTopSplit .binaryFour .ordinaryThree ?_ ?_
  · intro _hZmud p R N hbinary
    exact (Classical.choice
      (BinaryPairTernaryNormalizerPrefix.literal_binary_top_quotient_orbitInput
        PrimitiveAffineDegreeTwoTwelveRow32OriginalGeometry.literalTopCertificate
        R N hbinary)).anchor
  · intro hZmud p R N hnonbinary
    have hQ : ¬ IsPGroup 2 (preE7PairAction 12 p ⧸ N.1) := by
      intro hQ
      exact hnonbinary
        (hQ.of_surjective (R.quotientMap N) (R.quotientMap_surjective N))
    exact PrimitiveAffineDegreeTwoTwelveRow32OriginalSocle.nonbinary_quotient_anchor
      R hZmud N hQ

def resolvedRow (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization rowInterface p) :
    DegreeTwoPairTopResolvedRow rowInterface degreeTwoTwelvePairExceptionalProfiles p :=
  (certificate.resolvedData hZmud lit R).toResolvedRow

end PrimitiveAffineDegreeTwoTwelveRow32ExceptionalAssembly
end SymmetricSubgroupAsymptotics

end
