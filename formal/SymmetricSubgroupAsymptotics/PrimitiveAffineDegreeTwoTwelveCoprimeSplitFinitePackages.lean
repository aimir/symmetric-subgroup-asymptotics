import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSignedSplitFinitePackages
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveKleinSplitSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveKleinNaturalWitnesses
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow5NaturalFamily

/-! Complete packages for the signed cyclic, signed dihedral, Klein and
dihedral-product coprime families, with their original stored capacities. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveCoprimeSplitFinitePackages

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

def row2 : DegreeTwoTwelveJointFiniteRowData row2Interface 2 2 where
  topSocle := PrimitiveAffineDegreeTwoTwelveKleinSplitSocles.row2TopSocle
  natural := PrimitiveAffineDegreeTwoTwelveKleinNaturalWitnesses.row2Natural

def row16 : DegreeTwoTwelveJointFiniteRowData row16Interface 2 2 where
  topSocle := PrimitiveAffineDegreeTwoTwelveKleinSplitSocles.row16TopSocle
  natural := PrimitiveAffineDegreeTwoTwelveKleinNaturalWitnesses.row16Natural

def row18 : DegreeTwoTwelveJointFiniteRowData row18Interface 2 2 where
  topSocle := PrimitiveAffineDegreeTwoTwelveKleinSplitSocles.row18TopSocle
  natural := PrimitiveAffineDegreeTwoTwelveKleinNaturalWitnesses.row18Natural

def row70 : DegreeTwoTwelveJointFiniteRowData row70Interface 2 2 where
  topSocle := PrimitiveAffineDegreeTwoTwelveKleinSplitSocles.row70TopSocle
  natural := PrimitiveAffineDegreeTwoTwelveKleinNaturalWitnesses.row70Natural

def row71 : DegreeTwoTwelveJointFiniteRowData row71Interface 2 2 where
  topSocle := PrimitiveAffineDegreeTwoTwelveKleinSplitSocles.row71TopSocle
  natural := PrimitiveAffineDegreeTwoTwelveKleinNaturalWitnesses.row71Natural

def row130 : DegreeTwoTwelveJointFiniteRowData row130Interface 2 2 where
  topSocle := PrimitiveAffineDegreeTwoTwelveKleinSplitSocles.row130TopSocle
  natural := PrimitiveAffineDegreeTwoTwelveKleinNaturalWitnesses.row130Natural

def row5 : DegreeTwoTwelveJointFiniteRowData row5Interface 1 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSignedCyclicSocles.row5TopSocle
  natural := PrimitiveAffineDegreeTwoTwelveRow5NaturalFamily.row5Natural

def row13 : DegreeTwoTwelveJointFiniteRowData row13Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSignedDihedralSocles.row13TopSocle
  natural := PrimitiveAffineDegreeTwoTwelveRow5NaturalFamily.row13Natural

def row15 : DegreeTwoTwelveJointFiniteRowData row15Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSignedDihedralSocles.row15TopSocle
  natural := PrimitiveAffineDegreeTwoTwelveRow5NaturalFamily.row15Natural

def row28 : DegreeTwoTwelveJointFiniteRowData row28Interface 3 1 :=
  DegreeTwoTwelveSignedSplitFinitePackages.row28

def row73 : DegreeTwoTwelveJointFiniteRowData row73Interface 1 1 :=
  DegreeTwoTwelveSignedSplitFinitePackages.row73

def row118 : DegreeTwoTwelveJointFiniteRowData row118Interface 2 1 :=
  DegreeTwoTwelveSignedSplitFinitePackages.row118

def row121 : DegreeTwoTwelveJointFiniteRowData row121Interface 2 1 :=
  DegreeTwoTwelveSignedSplitFinitePackages.row121

def row156 : DegreeTwoTwelveJointFiniteRowData row156Interface 3 1 :=
  DegreeTwoTwelveSignedSplitFinitePackages.row156

def row217 : DegreeTwoTwelveJointFiniteRowData row217Interface 3 1 :=
  DegreeTwoTwelveSignedSplitFinitePackages.row217

end DegreeTwoTwelveCoprimeSplitFinitePackages
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
