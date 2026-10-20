import SymmetricSubgroupAsymptotics.TernaryFourBlockKleinSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150

/-! Six original twelve-point tops with a regular Klein-four block
complement. The six different actual translation spaces need no census. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveKleinSplitSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue TernaryFourBlockKleinSocles
open PrimitiveAffineDegreeTwoTwelveRow131AffineModel (Vector)

def constantSeed : Vector := fun _ ↦ 1
def alternatingSeed : Vector := fun i ↦ ![1, 0, 2, 0] i.toAdd
def pairedSeed : Vector := fun i ↦ ![1, 0, 1, 0] i.toAdd
def threeSeed : Vector := fun i ↦ ![1, 1, 1, 0] i.toAdd
def singleSeed : Vector := fun i ↦ ![1, 0, 0, 0] i.toAdd

def row2Index : Equiv.Perm (Fin 3) := Equiv.swap 0 2 * Equiv.swap 1 2

theorem row2_binding (i : Fin 3) :
    literalAction false (lifted false constantSeed i) = row2Generators (row2Index i) := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem row16_binding (i : Fin 3) :
    literalAction false (lifted false alternatingSeed i) = row16Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem row18_binding (i : Fin 3) :
    literalAction false (lifted false pairedSeed i) = row18Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem row70_binding (i : Fin 3) :
    literalAction true (lifted true threeSeed i) = row70Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem row71_binding (i : Fin 3) :
    literalAction false (lifted false threeSeed i) = row71Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem row130_binding (i : Fin 3) :
    literalAction false (lifted false singleSeed i) = row130Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

def row2TopSocle : row2Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle false constantSeed row2Generators row2Index row2_binding N.1)

def row16TopSocle : row16Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle false alternatingSeed row16Generators (Equiv.refl _) row16_binding N.1)

def row18TopSocle : row18Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle false pairedSeed row18Generators (Equiv.refl _) row18_binding N.1)

def row70TopSocle : row70Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle true threeSeed row70Generators (Equiv.refl _) row70_binding N.1)

def row71TopSocle : row71Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle false threeSeed row71Generators (Equiv.refl _) row71_binding N.1)

def row130TopSocle : row130Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle false singleSeed row130Generators (Equiv.refl _) row130_binding N.1)

end PrimitiveAffineDegreeTwoTwelveKleinSplitSocles
end SymmetricSubgroupAsymptotics

end
