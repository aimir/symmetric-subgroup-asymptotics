import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150

/-! The original second generator has two literal six-point orbits. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row147OriginalNaturalTwo
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def witness : LiteralCyclicOrbitWitness row147Interface.top 2 where
  element := closureGenerators row147Generators 1
  representative := ![0, 1]
  orbitIndex := ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
  exponent := ![0, 0, 3, 5, 2, 2, 5, 1, 4, 4, 1, 3]
  point_eq := by decide +kernel

theorem natural_two : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row147Interface.top (Fin 12)) 2 :=
  witness.uniform _

end SymmetricSubgroupAsymptotics.Row147OriginalNaturalTwo
