import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightSharedTops
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenInterfaces
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenInterfaces
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenInterfaces

/-!
# Concrete finite catalogue for sixteen pairs

This is the literal 24/29/15/20 action catalogue used by the count-sixteen
pair branch.  The 24 paired-eight entries reuse the earlier shared-top word
registries, including the previously completed thirty-row work.  The first
zero-core degree-sixteen entry likewise reuses its existing generated
normal registry.  Every remaining literal top is installed from the pinned
action alphabet with semantic normal and invariant-module registries.

The catalogue is therefore concrete and complete at the finite-interface
layer.  The only later inputs are the published top locator, the
per-original-quotient anchored relative-character theorem on each finite
row, and the natural `A_16`/`S_16` character alternative.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoSixteenPairFiniteCatalogue

noncomputable def catalogue : DegreeTwoSixteenPairTopFiniteCatalogue :=
  DegreeTwoPairedEightSharedTops.sixteenCatalogue
    DegreeTwoZeroSixteenInterfaces.interface
    DegreeTwoTwoAffineSixteenInterfaces.interface
    DegreeTwoPrimitiveSixteenInterfaces.interface

@[simp] theorem catalogue_paired8 (j : Fin 24) :
    catalogue.paired8 j = DegreeTwoPairedEightSharedTops.interface j := rfl

@[simp] theorem catalogue_zero16 (j : Fin 29) :
    catalogue.zero16 j = DegreeTwoZeroSixteenInterfaces.interface j := rfl

@[simp] theorem catalogue_twoAffine16 (j : Fin 15) :
    catalogue.twoAffine16 j =
      DegreeTwoTwoAffineSixteenInterfaces.interface j := rfl

@[simp] theorem catalogue_primitive16 (j : Fin 20) :
    catalogue.primitive16 j =
      DegreeTwoPrimitiveSixteenInterfaces.interface j := rfl

end DegreeTwoSixteenPairFiniteCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
