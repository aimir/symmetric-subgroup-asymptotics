import SymmetricSubgroupAsymptotics.TernaryFourBlockSplitLiteralSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200

/-! Eight literal split-subgroup consumers of the checked four-block
metacyclic model. Each binding is an equality on the original 12 points;
all eight original registry families retain their stored bound two. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveSplitMetacyclicSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open TernaryFourBlockSplitLiteralSocles
open PrimitiveAffineDegreeTwoTwelveRow131AffineModel (Block Vector)

def constantSeed : Vector := fun _ ↦ 1
def threeSeed : Vector := fun i ↦ ![1, 1, 1, 0] i.toAdd
def singleSeed : Vector := fun i ↦ ![1, 0, 0, 0] i.toAdd

theorem row12_binding (i : Fin 3) :
    literalAction true true (lifted true true constantSeed i) =
      row12Generators (Equiv.swap 1 2 i) := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem row14_binding (i : Fin 3) :
    literalAction true false (lifted true false constantSeed i) =
      row14Generators (Equiv.swap 0 2 i) := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem row116_binding (i : Fin 3) :
    literalAction true false (lifted true false threeSeed i) =
      row116Generators (Equiv.swap 1 2 i) := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem row119_binding (i : Fin 3) :
    literalAction false true (lifted false true threeSeed i) = row119Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem row120_binding (i : Fin 3) :
    literalAction true true (lifted true true threeSeed i) =
      row120Generators (Equiv.swap 1 2 i) := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem row167_binding (i : Fin 3) :
    literalAction true false (lifted true false singleSeed i) =
      row167Generators (Equiv.swap 1 2 i) := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem row169_binding (i : Fin 3) :
    literalAction true true (lifted true true singleSeed i) =
      row169Generators (Equiv.swap 1 2 i) := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem row170_binding (i : Fin 3) :
    literalAction false true (lifted false true singleSeed i) = row170Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

def row12TopSocle : row12Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle true true constantSeed row12Generators
      (Equiv.swap 1 2) row12_binding N.1)

def row14TopSocle : row14Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle true false constantSeed row14Generators
      (Equiv.swap 0 2) row14_binding N.1)

def row116TopSocle : row116Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle true false threeSeed row116Generators
      (Equiv.swap 1 2) row116_binding N.1)

def row119TopSocle : row119Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle false true threeSeed row119Generators
      (Equiv.refl _) row119_binding N.1)

def row120TopSocle : row120Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle true true threeSeed row120Generators
      (Equiv.swap 1 2) row120_binding N.1)

def row167TopSocle : row167Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle true false singleSeed row167Generators
      (Equiv.swap 1 2) row167_binding N.1)

def row169TopSocle : row169Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle true true singleSeed row169Generators
      (Equiv.swap 1 2) row169_binding N.1)

def row170TopSocle : row170Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle false true singleSeed row170Generators
      (Equiv.refl _) row170_binding N.1)

end PrimitiveAffineDegreeTwoTwelveSplitMetacyclicSocles
end SymmetricSubgroupAsymptotics

end
