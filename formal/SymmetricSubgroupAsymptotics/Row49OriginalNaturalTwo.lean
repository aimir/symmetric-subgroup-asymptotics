import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row49OriginalNaturalTwo
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
def witness : LiteralCyclicOrbitWitness Row49Top 2 where
  element := closureGenerators row49Generators 1 * closureGenerators row49Generators 2 *
    closureGenerators row49Generators 0
  representative := ![0,1]
  orbitIndex := ![0,1,0,0,0,1,1,1,0,0,1,1]
  exponent := ![0,0,1,5,4,4,3,1,3,2,5,2]
  point_eq := by decide +kernel
theorem natural_two : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row49Interface.top (Fin 12)) 2 :=
  witness.uniform _
end SymmetricSubgroupAsymptotics.Row49OriginalNaturalTwo
