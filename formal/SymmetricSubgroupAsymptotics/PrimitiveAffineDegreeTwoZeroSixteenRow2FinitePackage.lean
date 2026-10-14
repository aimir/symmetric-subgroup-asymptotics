import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow2OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow2QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenOneFrameFiniteRows

/-!
# Complete zero-sixteen row two from point orbits and a reused normal registry

The literal four-cycle witness supplies the natural-module bound. The
existing degree-four normal registry supplies two generators for every
original normal quotient socle. Their existing common consumer resolves
every realization of the unchanged degree-two top.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRow2FinitePackage

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoSixteenOneFrameFiniteRows

/-- Both required bounds on the actual literal top, with no capacity premise. -/
noncomputable def finiteData :
    DegreeTwoSixteenOneFrameFiniteRowData DegreeTwoZeroSixteenInterfaces.row2 :=
  .ofCertificates PrimitiveAffineDegreeTwoZeroSixteenRow2QuotientSocles.family
    PrimitiveAffineDegreeTwoZeroSixteenRow2OrbitWitness.interface_natural

/-- The same package at its original catalogue position. -/
noncomputable def catalogueFiniteData :
    DegreeTwoSixteenOneFrameFiniteRowData
      (DegreeTwoSixteenPairFiniteCatalogue.catalogue.zero16 (1 : Fin 29)) :=
  finiteData

/-- Every realization now needs only the published character inputs. -/
noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization DegreeTwoZeroSixteenInterfaces.row2 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoZeroSixteenInterfaces.row2
      degreeTwoSixteenPairProfiles p :=
  finiteData.resolvedRow hZmud lit R

end PrimitiveAffineDegreeTwoZeroSixteenRow2FinitePackage
end SymmetricSubgroupAsymptotics

end
