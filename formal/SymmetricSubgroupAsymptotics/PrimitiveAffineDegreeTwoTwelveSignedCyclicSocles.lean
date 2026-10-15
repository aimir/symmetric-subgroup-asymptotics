import SymmetricSubgroupAsymptotics.TernaryFourBlockSignedCyclicSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100

/-! The original quotients of rows 5 and 73 retain their stored bound one
through the same signed C4 action on four ternary blocks. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveSignedCyclicSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue TernaryFourBlockSignedCyclicSocles
open PrimitiveAffineDegreeTwoTwelveRow131AffineModel (Vector)

def constantSeed : Vector := fun _ ↦ 1
def threeSeed : Vector := fun i ↦ ![1, 1, 1, 0] i.toAdd

theorem row5_binding (i : Fin 3) :
    literalAction (lifted constantSeed i) = row5Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem row73_binding (i : Fin 3) :
    literalAction (lifted threeSeed i) = row73Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

def row5TopSocle : row5Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle constantSeed row5Generators row5_binding N.1)

def row73TopSocle : row73Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle threeSeed row73Generators row73_binding N.1)

end PrimitiveAffineDegreeTwoTwelveSignedCyclicSocles
end SymmetricSubgroupAsymptotics

end
