import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow23OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow23CoverQuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenOneFrameFiniteRows

/-!
# Complete selected zero16 row 23

The existing orbit witness and the conjugacy-cover normal registry retain
the actual literal top and every original normal quotient.
This source requires a bounded Lean check and a standard-axiom audit.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRow23FinitePackage

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoSixteenOneFrameFiniteRows

noncomputable def finiteData :
    DegreeTwoSixteenOneFrameFiniteRowData DegreeTwoZeroSixteenInterfaces.row23 :=
  .ofCertificates PrimitiveAffineDegreeTwoZeroSixteenRow23CoverQuotientSocles.family
    PrimitiveAffineDegreeTwoZeroSixteenRow23OrbitWitness.natural

noncomputable def catalogueFiniteData :
    DegreeTwoSixteenOneFrameFiniteRowData
      (DegreeTwoSixteenPairFiniteCatalogue.catalogue.zero16 (22 : Fin 29)) :=
  finiteData

noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization DegreeTwoZeroSixteenInterfaces.row23 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoZeroSixteenInterfaces.row23
      degreeTwoSixteenPairProfiles p :=
  finiteData.resolvedRow hZmud lit R

end PrimitiveAffineDegreeTwoZeroSixteenRow23FinitePackage
end SymmetricSubgroupAsymptotics

end
