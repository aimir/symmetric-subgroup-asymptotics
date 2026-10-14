import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow131ImageSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50

/-!
# Two more literal coprime cyclic quotient-socle fields

On the four ternary blocks, `I - rotate₂` sends the local delta vector
to `(1,0,2,0)`, and `I + rotate₂` sends it to `(1,0,1,0)`. These are the
original row-17 and row-19 translations. Both maps fix the displayed
four-cycle, so the shared image consumer applies to the exact tops.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRows17And19ImageSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open PrimitiveAffineDegreeTwoTwelveRow131AffineModel
open PrimitiveAffineDegreeTwoTwelveRow131ImageSocles

private theorem linearAction_commute (c d : Block) (v : Vector) :
    linearAction c (linearAction d v) = linearAction d (linearAction c v) := by
  calc
    linearAction c (linearAction d v) = linearAction (c * d) v :=
      (LinearEquiv.congr_fun (linearAction.map_mul c d) v).symm
    _ = linearAction (d * c) v := by rw [mul_comm c d]
    _ = linearAction d (linearAction c v) :=
      LinearEquiv.congr_fun (linearAction.map_mul d c) v

def row17Projection : Vector →ₗ[ZMod 3] Vector :=
  LinearMap.id - (linearAction (Multiplicative.ofAdd 2)).toLinearMap

theorem row17Projection_equivariant (c : Block) (v : Vector) :
    row17Projection (linearAction c v) = linearAction c (row17Projection v) := by
  change linearAction c v - linearAction (Multiplicative.ofAdd 2) (linearAction c v) =
    linearAction c (v - linearAction (Multiplicative.ofAdd 2) v)
  rw [map_sub, linearAction_commute (Multiplicative.ofAdd 2) c]

theorem row17_binding (i : Fin 2) :
    literalMap row17Projection row17Projection_equivariant (modelGenerators i) =
      row17Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def row19Projection : Vector →ₗ[ZMod 3] Vector :=
  LinearMap.id + (linearAction (Multiplicative.ofAdd 2)).toLinearMap

theorem row19Projection_equivariant (c : Block) (v : Vector) :
    row19Projection (linearAction c v) = linearAction c (row19Projection v) := by
  change linearAction c v + linearAction (Multiplicative.ofAdd 2) (linearAction c v) =
    linearAction c (v + linearAction (Multiplicative.ofAdd 2) v)
  rw [map_add, linearAction_commute (Multiplicative.ofAdd 2) c]

theorem row19_binding (i : Fin 2) :
    literalMap row19Projection row19Projection_equivariant (modelGenerators i) =
      row19Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def row17TopSocle : row17Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle row17Projection row17Projection_equivariant row17Generators
      row17_binding N.1)

def row19TopSocle : row19Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle row19Projection row19Projection_equivariant row19Generators
      row19_binding N.1)

end PrimitiveAffineDegreeTwoTwelveRows17And19ImageSocles
end SymmetricSubgroupAsymptotics

end
