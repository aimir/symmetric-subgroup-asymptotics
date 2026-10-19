import SymmetricSubgroupAsymptotics.Row62OriginalQuartetFrame
import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row62OriginalNaturalTwo
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def witness : LiteralCyclicOrbitWitness Row62Top 2 where
  element := closureGenerators row62Generators 0 * closureGenerators row62Generators 2
  representative := ![0,2]
  orbitIndex := ![0,0,1,0,0,1,0,0,1,0,0,1]
  exponent := ![0,3,0,6,1,1,4,7,2,2,5,3]
  point_eq := by decide +kernel

theorem natural_two : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row62Interface.top (Fin 12)) 2 :=
  witness.uniform _
end SymmetricSubgroupAsymptotics.Row62OriginalNaturalTwo
