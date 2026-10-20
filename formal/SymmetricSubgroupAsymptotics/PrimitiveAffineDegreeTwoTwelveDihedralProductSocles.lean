import SymmetricSubgroupAsymptotics.TernaryFourBlockDihedralProductSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-! Three exact original tuples for the dihedral block action with an
independent scalar sign. All original registry bounds remain three. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveDihedralProductSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue TernaryFourBlockDihedralProductSocles
open PrimitiveAffineDegreeTwoTwelveRow131AffineModel (Vector)

def constantSeed : Vector := fun _ ↦ 1
def threeSeed : Vector := fun i ↦ ![1, 1, 1, 0] i.toAdd
def singleSeed : Vector := fun i ↦ ![1, 0, 0, 0] i.toAdd

def row28Index : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 2
def signFirstIndex : Equiv.Perm (Fin 4) := Equiv.swap 1 3 * Equiv.swap 1 2

theorem row28_binding (i : Fin 4) :
    literalAction (lifted constantSeed i) = row28Generators (row28Index i) := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem row156_binding (i : Fin 4) :
    literalAction (lifted threeSeed i) = row156Generators (signFirstIndex i) := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem row217_binding (i : Fin 4) :
    literalAction (lifted singleSeed i) = row217Generators (signFirstIndex i) := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

def row28TopSocle : row28Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle constantSeed row28Generators row28Index row28_binding N.1)

def row156TopSocle : row156Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle threeSeed row156Generators signFirstIndex row156_binding N.1)

def row217TopSocle : row217Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle singleSeed row217Generators signFirstIndex row217_binding N.1)

end PrimitiveAffineDegreeTwoTwelveDihedralProductSocles
end SymmetricSubgroupAsymptotics

end
