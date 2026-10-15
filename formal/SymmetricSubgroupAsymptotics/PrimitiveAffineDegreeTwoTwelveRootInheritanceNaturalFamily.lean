import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow5NaturalFamily
import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-! Two root witnesses close five further original natural fields.
Rows30/98 contain the exact row5 generators; its middle generator is the
square of its last generator. Row126 has a prescribed element with two
six-point cycles, and rows161/203 contain its literal generating tuple.
All embeddings retain the original point chart and stored capacities. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRootInheritanceNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def row30Embedding : LiteralPermutationGeneratorEmbedding row5Generators Row30Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row30Generators 1, (closureGenerators row30Generators 2) ^ 2,
    closureGenerators row30Generators 2]
  point_eq := by decide +kernel

def row98Embedding : LiteralPermutationGeneratorEmbedding row5Generators Row98Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row98Generators 2, (closureGenerators row98Generators 3) ^ 2,
    closureGenerators row98Generators 3]
  point_eq := by decide +kernel

theorem row30Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row30Interface.top (Fin 12)) 1 :=
  row30Embedding.uniform PrimitiveAffineDegreeTwoTwelveRow5NaturalFamily.row5Natural

theorem row98Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row98Interface.top (Fin 12)) 1 :=
  row98Embedding.uniform PrimitiveAffineDegreeTwoTwelveRow5NaturalFamily.row5Natural

def row126Witness : LiteralCyclicOrbitWitness Row126Top 2 where
  element := closureGenerators row126Generators 1 * closureGenerators row126Generators 2
  representative := ![0, 1]
  orbitIndex := ![0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0]
  exponent := ![0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5]
  point_eq := by decide +kernel

theorem row126Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row126Interface.top (Fin 12)) 2 :=
  row126Witness.uniform _

def row161Embedding : LiteralPermutationGeneratorEmbedding row126Generators Row161Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row161Generators 0, closureGenerators row161Generators 1,
    closureGenerators row161Generators 3]
  point_eq := by decide +kernel

def row203Embedding : LiteralPermutationGeneratorEmbedding row126Generators Row203Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row203Generators 0, closureGenerators row203Generators 1,
    closureGenerators row203Generators 3]
  point_eq := by decide +kernel

theorem row161Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row161Interface.top (Fin 12)) 2 :=
  row161Embedding.uniform row126Natural

theorem row203Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row203Interface.top (Fin 12)) 2 :=
  row203Embedding.uniform row126Natural

end PrimitiveAffineDegreeTwoTwelveRootInheritanceNaturalFamily
end SymmetricSubgroupAsymptotics

end
