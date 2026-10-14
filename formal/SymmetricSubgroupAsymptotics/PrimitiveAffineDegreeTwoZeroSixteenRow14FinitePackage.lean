import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow14OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow14QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenOneFrameFiniteRows

/-!
# Complete selected zero16 row 14

Prepared by `prepare_lean_selected_pair_registry_sources.py`. The existing
orbit witness and the reused normal registry retain the actual literal top.
This source requires a bounded Lean check and a standard-axiom audit.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRow14FinitePackage

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoSixteenOneFrameFiniteRows

noncomputable def finiteData :
    DegreeTwoSixteenOneFrameFiniteRowData DegreeTwoZeroSixteenInterfaces.row14 :=
  .ofCertificates PrimitiveAffineDegreeTwoZeroSixteenRow14QuotientSocles.family
    PrimitiveAffineDegreeTwoZeroSixteenRow14OrbitWitness.natural

noncomputable def catalogueFiniteData :
    DegreeTwoSixteenOneFrameFiniteRowData
      (DegreeTwoSixteenPairFiniteCatalogue.catalogue.zero16 (13 : Fin 29)) :=
  finiteData

noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization DegreeTwoZeroSixteenInterfaces.row14 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoZeroSixteenInterfaces.row14
      degreeTwoSixteenPairProfiles p :=
  finiteData.resolvedRow hZmud lit R

end PrimitiveAffineDegreeTwoZeroSixteenRow14FinitePackage
end SymmetricSubgroupAsymptotics

end
