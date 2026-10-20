import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwoTernaryMatrixNaturalPilot
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwoTernaryMatrixNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveLocalWreathPairImageSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwoTernaryPairImageSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles

/-! Three original joint actions share the two-ternary matrix natural
bound and the actual local wreath pair-image socle bound. The proved
alternate profile is (3,1); the historical (2,1) records are unchanged. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveTwoTernaryMatrixFinitePackages

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

/-- Original row201, zero-based index200, joint; historical (2,1). -/
def row201At3 : DegreeTwoTwelveJointFiniteRowData row201Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveLocalWreathPairImageSocles.row201AtThree_family
  natural := PrimitiveAffineDegreeTwoTwelveTwoTernaryMatrixNaturalPilot.row201Natural

noncomputable def row201At3Data : DegreeTwoTwelveFlexibleProfiles.Data row201Interface :=
  .ofExact row201At3 (by decide +kernel)

/-- Original row237, zero-based index236, joint; historical (2,1). -/
def row237At3 : DegreeTwoTwelveJointFiniteRowData row237Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveTwoTernaryPairImageSocles.row237AtThree_family
  natural := PrimitiveAffineDegreeTwoTwelveTwoTernaryMatrixNaturalFamily.row237Natural

noncomputable def row237At3Data : DegreeTwoTwelveFlexibleProfiles.Data row237Interface :=
  .ofExact row237At3 (by decide +kernel)

/-- Original row238, zero-based index237, joint; historical (2,1). -/
def row238At3 : DegreeTwoTwelveJointFiniteRowData row238Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveTwoTernaryPairImageSocles.row238AtThree_family
  natural := PrimitiveAffineDegreeTwoTwelveTwoTernaryMatrixNaturalFamily.row238Natural

noncomputable def row238At3Data : DegreeTwoTwelveFlexibleProfiles.Data row238Interface :=
  .ofExact row238At3 (by decide +kernel)

end DegreeTwoTwelveTwoTernaryMatrixFinitePackages
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
