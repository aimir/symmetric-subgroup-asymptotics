import SymmetricSubgroupAsymptotics.TernaryFourBlockSignedDihedralSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150

/-! Four exact original tuples for the signed dihedral block action. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveSignedDihedralSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue TernaryFourBlockSignedDihedralSocles
open PrimitiveAffineDegreeTwoTwelveRow131AffineModel (Vector)

def constantSeed : Vector := fun _ ↦ 1
def threeSeed : Vector := fun i ↦ ![1, 1, 1, 0] i.toAdd

theorem row13_binding (i : Fin 4) :
    literalAction true (lifted true constantSeed i) = row13Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem row15_binding (i : Fin 4) :
    literalAction false (lifted false constantSeed i) = row15Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem row118_binding (i : Fin 4) :
    literalAction true (lifted true threeSeed i) = row118Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem row121_binding (i : Fin 4) :
    literalAction false (lifted false threeSeed i) = row121Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

def row13TopSocle : row13Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle true constantSeed row13Generators row13_binding N.1)

def row15TopSocle : row15Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle false constantSeed row15Generators row15_binding N.1)

def row118TopSocle : row118Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle true threeSeed row118Generators row118_binding N.1)

def row121TopSocle : row121Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle false threeSeed row121Generators row121_binding N.1)

end PrimitiveAffineDegreeTwoTwelveSignedDihedralSocles
end SymmetricSubgroupAsymptotics

end
