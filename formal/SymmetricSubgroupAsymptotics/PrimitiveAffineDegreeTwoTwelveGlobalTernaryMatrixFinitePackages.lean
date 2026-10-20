import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveGlobalTernaryMatrixNaturalPilot
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveGlobalTernaryPairImageSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles

/-! Original row54 has natural capacity one by global-ternary matrix blocks
and quotient-socle capacity three from its actual dihedral pair image.
This gives alternate profile (3,1) for its historical (2,1) joint record. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveGlobalTernaryMatrixFinitePackages

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

/-- Original row54, zero-based index53, joint; historical (2,1). -/
def row54At3 : DegreeTwoTwelveJointFiniteRowData row54Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveGlobalTernaryPairImageSocles.row54AtThree_family
  natural := PrimitiveAffineDegreeTwoTwelveGlobalTernaryMatrixNaturalPilot.row54Natural

noncomputable def row54At3Data : DegreeTwoTwelveFlexibleProfiles.Data row54Interface :=
  .ofExact row54At3 (by decide +kernel)

end DegreeTwoTwelveGlobalTernaryMatrixFinitePackages
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
