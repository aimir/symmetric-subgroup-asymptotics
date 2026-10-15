import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow22OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow22QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenOneFrameFiniteRows

/-!
# Complete selected zero16 row 22

Prepared by `prepare_lean_selected_pair_registry_sources.py`. The existing
orbit witness and the reused normal registry retain the actual literal top.
This source requires a bounded Lean check and a standard-axiom audit.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRow22FinitePackage

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoSixteenOneFrameFiniteRows

noncomputable def finiteData :
    DegreeTwoSixteenOneFrameFiniteRowData DegreeTwoZeroSixteenInterfaces.row22 :=
  .ofCertificates PrimitiveAffineDegreeTwoZeroSixteenRow22QuotientSocles.family
    PrimitiveAffineDegreeTwoZeroSixteenRow22OrbitWitness.natural

noncomputable def catalogueFiniteData :
    DegreeTwoSixteenOneFrameFiniteRowData
      (DegreeTwoSixteenPairFiniteCatalogue.catalogue.zero16 (21 : Fin 29)) :=
  finiteData

noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization DegreeTwoZeroSixteenInterfaces.row22 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoZeroSixteenInterfaces.row22
      degreeTwoSixteenPairProfiles p :=
  finiteData.resolvedRow hZmud lit R

end PrimitiveAffineDegreeTwoZeroSixteenRow22FinitePackage
end SymmetricSubgroupAsymptotics

end
