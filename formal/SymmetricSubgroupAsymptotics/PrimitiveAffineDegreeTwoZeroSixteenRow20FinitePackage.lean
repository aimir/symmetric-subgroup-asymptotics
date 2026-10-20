import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow20OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow20QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenOneFrameFiniteRows

/-!
# Complete selected zero16 row 20

Prepared by `prepare_lean_selected_pair_registry_sources.py`. The existing
orbit witness and the reused normal registry retain the actual literal top.
This source requires a bounded Lean check and a standard-axiom audit.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRow20FinitePackage

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoSixteenOneFrameFiniteRows

noncomputable def finiteData :
    DegreeTwoSixteenOneFrameFiniteRowData DegreeTwoZeroSixteenInterfaces.row20 :=
  .ofCertificates PrimitiveAffineDegreeTwoZeroSixteenRow20QuotientSocles.family
    PrimitiveAffineDegreeTwoZeroSixteenRow20OrbitWitness.natural

noncomputable def catalogueFiniteData :
    DegreeTwoSixteenOneFrameFiniteRowData
      (DegreeTwoSixteenPairFiniteCatalogue.catalogue.zero16 (19 : Fin 29)) :=
  finiteData

noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization DegreeTwoZeroSixteenInterfaces.row20 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoZeroSixteenInterfaces.row20
      degreeTwoSixteenPairProfiles p :=
  finiteData.resolvedRow hZmud lit R

end PrimitiveAffineDegreeTwoZeroSixteenRow20FinitePackage
end SymmetricSubgroupAsymptotics

end
