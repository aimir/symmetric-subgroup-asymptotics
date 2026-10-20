import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow11SplitSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSplitMetacyclicSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSharedNaturalWitnesses
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow72PolynomialFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow131CyclicFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointFiniteRows

/-! Complete packages for nine original joint actions. All original
normal quotients and stored capacities are retained; the shared coprime
retraction supplies the socle fields and existing literal module proofs
supply their one-generator natural fields. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveSplitMetacyclicFinitePackages

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

def row11 : DegreeTwoTwelveJointFiniteRowData row11Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveRow11SplitSocles.row11TopSocle
  natural := DegreeTwoTwelveSharedNaturalWitnesses.row11Natural

def row12 : DegreeTwoTwelveJointFiniteRowData row12Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSplitMetacyclicSocles.row12TopSocle
  natural := DegreeTwoTwelveSharedNaturalWitnesses.row12Natural

def row14 : DegreeTwoTwelveJointFiniteRowData row14Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSplitMetacyclicSocles.row14TopSocle
  natural := DegreeTwoTwelveSharedNaturalWitnesses.row14Natural

def row116 : DegreeTwoTwelveJointFiniteRowData row116Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSplitMetacyclicSocles.row116TopSocle
  natural := DegreeTwoTwelveRow72PolynomialFamily.row116Natural

def row119 : DegreeTwoTwelveJointFiniteRowData row119Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSplitMetacyclicSocles.row119TopSocle
  natural := DegreeTwoTwelveRow72PolynomialFamily.row119Natural

def row120 : DegreeTwoTwelveJointFiniteRowData row120Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSplitMetacyclicSocles.row120TopSocle
  natural := DegreeTwoTwelveRow72PolynomialFamily.row120Natural

def row167 : DegreeTwoTwelveJointFiniteRowData row167Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSplitMetacyclicSocles.row167TopSocle
  natural := DegreeTwoTwelveRow131CyclicFamily.row167Natural

def row169 : DegreeTwoTwelveJointFiniteRowData row169Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSplitMetacyclicSocles.row169TopSocle
  natural := DegreeTwoTwelveRow131CyclicFamily.row169Natural

def row170 : DegreeTwoTwelveJointFiniteRowData row170Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSplitMetacyclicSocles.row170TopSocle
  natural := DegreeTwoTwelveRow131CyclicFamily.row170Natural

end DegreeTwoTwelveSplitMetacyclicFinitePackages
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
