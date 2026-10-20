import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow26OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow26CoverQuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenOneFrameFiniteRows

/-!
# Complete selected zero16 row 26

Prepared by `prepare_lean_selected_pair_registry_sources.py`. The existing
orbit witness and the reused normal registry retain the actual literal top.
This source requires a bounded Lean check and a standard-axiom audit.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRow26FinitePackage

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoSixteenOneFrameFiniteRows

noncomputable def finiteData :
    DegreeTwoSixteenOneFrameFiniteRowData DegreeTwoZeroSixteenInterfaces.row26 :=
  .ofCertificates PrimitiveAffineDegreeTwoZeroSixteenRow26CoverQuotientSocles.family
    PrimitiveAffineDegreeTwoZeroSixteenRow26OrbitWitness.natural

noncomputable def catalogueFiniteData :
    DegreeTwoSixteenOneFrameFiniteRowData
      (DegreeTwoSixteenPairFiniteCatalogue.catalogue.zero16 (25 : Fin 29)) :=
  finiteData

noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 16}
    (R : DegreeTwoPairTopRealization DegreeTwoZeroSixteenInterfaces.row26 p) :
    DegreeTwoPairTopResolvedRow DegreeTwoZeroSixteenInterfaces.row26
      degreeTwoSixteenPairProfiles p :=
  finiteData.resolvedRow hZmud lit R

end PrimitiveAffineDegreeTwoZeroSixteenRow26FinitePackage
end SymmetricSubgroupAsymptotics

end
