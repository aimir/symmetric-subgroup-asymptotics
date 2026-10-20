import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenFourByFourCharts
import SymmetricSubgroupAsymptotics.ProductBlockMatchingClosure

/-! Matching covariance holds for every element of the original literal
actions, by closure from the four generators. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenMatchingClosure
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoZeroSixteenFourByFourCharts

def row28Colour (x y : Fin 16) : Fin 4 :=
  row28MatchingLabel (coordinates.symm x).1
    (matchingColor (coordinates.symm x).2 (coordinates.symm y).2)

theorem row28_generator_matching : ∀ j,
    ProductBlockFrame.MatchingPreserves coordinates row28Colour
      (DegreeTwoZeroSixteenInterfaces.row28Generators j) (row28Tops j) := by
  unfold ProductBlockFrame.MatchingPreserves
  decide +kernel

/-- The original action transports the actual matching labels by its top. -/
theorem row28_matching (u : DegreeTwoZeroSixteenInterfaces.Row28Top) :
    ProductBlockFrame.MatchingPreserves coordinates row28Colour
      (u : Equiv.Perm (Fin 16)) (row28Frame.top u) :=
  ProductBlockFrame.ofGenerators_matching coordinates row28Colour
    DegreeTwoZeroSixteenInterfaces.row28Generators row28Tops
    row28_preserves row28_generator_matching u


def row29Colour (x y : Fin 16) : Fin 4 :=
  row29MatchingLabel (coordinates.symm x).1
    (matchingColor (coordinates.symm x).2 (coordinates.symm y).2)

theorem row29_generator_matching : ∀ j,
    ProductBlockFrame.MatchingPreserves coordinates row29Colour
      (DegreeTwoZeroSixteenInterfaces.row29Generators j) (row29Tops j) := by
  unfold ProductBlockFrame.MatchingPreserves
  decide +kernel

/-- The original action transports the actual matching labels by its top. -/
theorem row29_matching (u : DegreeTwoZeroSixteenInterfaces.Row29Top) :
    ProductBlockFrame.MatchingPreserves coordinates row29Colour
      (u : Equiv.Perm (Fin 16)) (row29Frame.top u) :=
  ProductBlockFrame.ofGenerators_matching coordinates row29Colour
    DegreeTwoZeroSixteenInterfaces.row29Generators row29Tops
    row29_preserves row29_generator_matching u

end PrimitiveAffineDegreeTwoZeroSixteenMatchingClosure
end SymmetricSubgroupAsymptotics
end
