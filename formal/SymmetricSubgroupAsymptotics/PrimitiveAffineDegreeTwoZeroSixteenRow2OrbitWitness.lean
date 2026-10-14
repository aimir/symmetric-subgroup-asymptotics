import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRow2OrbitCover

/-!
# An explicit sixteen-point witness for zero16 row 2

This wrapper retains the checked pilot's literal top, generator, and four
representatives. Two displayed sixteen-entry arrays assign each original
point to its representative and exponent. The finite check has no existential
search. Quotient-socle bounds remain separate from this natural-module bound.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRow2OrbitWitness

/-- Each point's position among the four representatives. -/
def orbitIndex : Fin 16 → Fin 4 :=
  ![0, 1, 1, 0, 2, 3, 2, 3, 1, 1, 0, 0, 3, 2, 3, 2]

/-- Each point's exponent from its assigned representative. -/
def exponent : Fin 16 → Fin 16 :=
  ![0, 0, 2, 2, 0, 0, 2, 2, 3, 1, 3, 1, 3, 3, 1, 1]

/-- The exact original subgroup carries the literal cyclic point witness. -/
def witness : LiteralCyclicOrbitWitness
    PrimitiveAffineDegreeTwoZeroSixteenRow2OrbitCover.Top 4 where
  element := PrimitiveAffineDegreeTwoZeroSixteenRow2OrbitCover.generator
  representative := PrimitiveAffineDegreeTwoZeroSixteenRow2OrbitCover.representatives
  orbitIndex := orbitIndex
  exponent := exponent
  point_eq := by decide +kernel

/-- Uniform four-generation obtained through the reusable witness API. -/
theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2)
      PrimitiveAffineDegreeTwoZeroSixteenRow2OrbitCover.Top (Fin 16)) 4 :=
  witness.uniform (ZMod 2)

/-- The conclusion keeps the literal finite-interface top unchanged. -/
theorem interface_natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2)
      Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row2.top
      (Fin 16)) 4 :=
  natural

end PrimitiveAffineDegreeTwoZeroSixteenRow2OrbitWitness
end SymmetricSubgroupAsymptotics

end
