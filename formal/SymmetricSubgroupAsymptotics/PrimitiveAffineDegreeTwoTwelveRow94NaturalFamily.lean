import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.PermutationNaturalBoundPointEmbedding
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301

/-!
# A local four-cycle and a three-block cycle in twelve original tops

The first row94 generator is the local cycle (2,5,8,11), and the second
cycles the three residue classes modulo 3. Their product is a twelve-cycle.
Eleven further literal tuples contain both generators unchanged, so the
same cyclic natural-module bound applies to their exact tops.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveRow94NaturalFamily

open DegreeTwoTwelvePairFiniteCatalogue

def witness : LiteralCyclicOrbitWitness Row94Top 1 where
  element := closureGenerators row94Generators 0 * closureGenerators row94Generators 1
  representative := fun _ ↦ 0
  orbitIndex := fun _ ↦ 0
  exponent := ![0, 10, 5, 3, 1, 8, 6, 4, 11, 9, 7, 2]
  point_eq := by decide +kernel

theorem row94Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row94Interface.top (Fin 12)) 1 :=
  witness.uniform _

def row141Embedding : LiteralPermutationGeneratorEmbedding row94Generators Row141Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row141Generators 0, closureGenerators row141Generators 2]
  point_eq := by decide +kernel

def row150Embedding : LiteralPermutationGeneratorEmbedding row94Generators Row150Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row150Generators 0, closureGenerators row150Generators 1]
  point_eq := by decide +kernel

def row151Embedding : LiteralPermutationGeneratorEmbedding row94Generators Row151Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row151Generators 0, closureGenerators row151Generators 1]
  point_eq := by decide +kernel

def row185Embedding : LiteralPermutationGeneratorEmbedding row94Generators Row185Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row185Generators 0, closureGenerators row185Generators 2]
  point_eq := by decide +kernel

def row189Embedding : LiteralPermutationGeneratorEmbedding row94Generators Row189Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row189Generators 0, closureGenerators row189Generators 2]
  point_eq := by decide +kernel

def row221Embedding : LiteralPermutationGeneratorEmbedding row94Generators Row221Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row221Generators 0, closureGenerators row221Generators 2]
  point_eq := by decide +kernel

def row222Embedding : LiteralPermutationGeneratorEmbedding row94Generators Row222Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row222Generators 0, closureGenerators row222Generators 2]
  point_eq := by decide +kernel

def row225Embedding : LiteralPermutationGeneratorEmbedding row94Generators Row225Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row225Generators 0, closureGenerators row225Generators 2]
  point_eq := by decide +kernel

def row250Embedding : LiteralPermutationGeneratorEmbedding row94Generators Row250Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row250Generators 0, closureGenerators row250Generators 2]
  point_eq := by decide +kernel

def row292Embedding : LiteralPermutationGeneratorEmbedding row94Generators Row292Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row292Generators 0, closureGenerators row292Generators 2]
  point_eq := by decide +kernel

def row294Embedding : LiteralPermutationGeneratorEmbedding row94Generators Row294Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row294Generators 0, closureGenerators row294Generators 2]
  point_eq := by decide +kernel

theorem row141Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row141Interface.top (Fin 12)) 1 :=
  row141Embedding.uniform row94Natural

theorem row150Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row150Interface.top (Fin 12)) 1 :=
  row150Embedding.uniform row94Natural

theorem row151Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row151Interface.top (Fin 12)) 1 :=
  row151Embedding.uniform row94Natural

theorem row185Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row185Interface.top (Fin 12)) 1 :=
  row185Embedding.uniform row94Natural

theorem row189Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row189Interface.top (Fin 12)) 1 :=
  row189Embedding.uniform row94Natural

theorem row221Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row221Interface.top (Fin 12)) 1 :=
  row221Embedding.uniform row94Natural

theorem row222Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row222Interface.top (Fin 12)) 1 :=
  row222Embedding.uniform row94Natural

theorem row225Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row225Interface.top (Fin 12)) 1 :=
  row225Embedding.uniform row94Natural

theorem row250Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row250Interface.top (Fin 12)) 1 :=
  row250Embedding.uniform row94Natural

theorem row292Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row292Interface.top (Fin 12)) 1 :=
  row292Embedding.uniform row94Natural

theorem row294Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row294Interface.top (Fin 12)) 1 :=
  row294Embedding.uniform row94Natural

end DegreeTwoTwelveRow94NaturalFamily
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
