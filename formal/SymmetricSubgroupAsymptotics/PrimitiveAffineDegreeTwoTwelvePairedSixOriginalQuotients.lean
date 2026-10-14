import SymmetricSubgroupAsymptotics.PairedSixQuotientAlternatives
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedSixGeometry
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedSixCyclicAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveInstalledCores

/-!
# The two literal paired-six original-quotient certificates

Each actual twelve-point top has its proved second pair frame. The
last six-point top supplies the cyclic natural-module theorem and the
one-ordinary-or-two-binary quotient alternative. The common consumer
therefore resolves every original normal quotient with the existing
exceptional profile menu.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelvePairedSixOriginalQuotients

open DegreeTwoTwelvePairFiniteCatalogue
open DegreeTwoTwelveExceptionalOriginalQuotients

def row195Certificate : RowCertificate row195Interface :=
  DegreeTwoTwelvePairedSixCyclicAssembly.certificate
    DegreeTwoTwelvePairedSixGeometry.row195
    (DegreeTwoTwelvePairedSixNaturalModules.first_uniform (ZMod 2))
    PairedSixQuotientAlternatives.first_family

def row236Certificate : RowCertificate row236Interface :=
  DegreeTwoTwelvePairedSixCyclicAssembly.certificate
    DegreeTwoTwelvePairedSixGeometry.row236
    (DegreeTwoTwelvePairedSixNaturalModules.second_uniform (ZMod 2))
    PairedSixQuotientAlternatives.second_family

def pairedData : DegreeTwoTwelveInstalledCores.RemainingPairedData where
  row195 := row195Certificate
  row236 := row236Certificate

/-- All ten exceptional relative rows, combining the eight installed
core certificates with the two literal paired-six certificates. -/
def exceptionalCatalogueData : CatalogueData catalogue := pairedData.catalogueData

def row195Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization row195Interface p) :
    DegreeTwoPairTopResolvedRow row195Interface degreeTwoTwelvePairExceptionalProfiles p :=
  (row195Certificate.resolvedData hZmud lit R).toResolvedRow

def row236Resolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization row236Interface p) :
    DegreeTwoPairTopResolvedRow row236Interface degreeTwoTwelvePairExceptionalProfiles p :=
  (row236Certificate.resolvedData hZmud lit R).toResolvedRow

end DegreeTwoTwelvePairedSixOriginalQuotients
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
