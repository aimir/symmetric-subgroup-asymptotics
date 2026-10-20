import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow1AlgebraPolynomial
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow1QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenOneFrameFiniteRows

/-!
# Complete first zero-core sixteen-point row

Four polynomial generators for one explicit group-algebra operator bound
every invariant submodule of the original point action. The existing
eight-state normal registry, now checked entirely by the kernel, bounds
the socle of every original normal quotient by two generators.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRow1FinitePackage

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoSixteenOneFrameFiniteRows

/-- Both required bounds on the actual literal top, with no capacity premise. -/
noncomputable def finiteData :
    DegreeTwoSixteenOneFrameFiniteRowData DegreeTwoZeroSixteenInterfaces.row1 :=
  .ofCertificates PrimitiveAffineDegreeTwoZeroSixteenRow1QuotientSocles.family
    PrimitiveAffineDegreeTwoZeroSixteenRow1AlgebraPolynomial.natural

/-- The same package at its original catalogue position. -/
noncomputable def catalogueFiniteData :
    DegreeTwoSixteenOneFrameFiniteRowData
      (DegreeTwoSixteenPairFiniteCatalogue.catalogue.zero16 (0 : Fin 29)) :=
  finiteData

/-- Every realization now needs only the published character inputs. -/
noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization DegreeTwoZeroSixteenInterfaces.row1 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoZeroSixteenInterfaces.row1
      degreeTwoSixteenPairProfiles p :=
  finiteData.resolvedRow hZmud lit R

end PrimitiveAffineDegreeTwoZeroSixteenRow1FinitePackage
end SymmetricSubgroupAsymptotics

end
