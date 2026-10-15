import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200

/-! An odd-offset lift of a six-pair cycle is a twelve-point cycle.
Five original actions realize this common cyclic/PID template by short
structural words: a paired ternary shift followed by a local pair swap,
or an odd kernel flip followed by the listed six-pair cycle. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveOddPairCycleWordNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def row99Witness : LiteralCyclicOrbitWitness Row99Top 1 where
  element := closureGenerators row99Generators 1 * closureGenerators row99Generators 3
  representative := ![0]
  orbitIndex := fun _ ↦ 0
  exponent := ![0, 3, 9, 7, 1, 10, 4, 2, 8, 11, 5, 6]
  point_eq := by decide +kernel

def row104Witness : LiteralCyclicOrbitWitness Row104Top 1 where
  element := closureGenerators row104Generators 1 * closureGenerators row104Generators 2
  representative := ![0]
  orbitIndex := fun _ ↦ 0
  exponent := ![0, 9, 3, 7, 1, 10, 4, 8, 2, 5, 11, 6]
  point_eq := by decide +kernel

def row143Witness : LiteralCyclicOrbitWitness Row143Top 1 where
  element := closureGenerators row143Generators 1 * closureGenerators row143Generators 2
  representative := ![0]
  orbitIndex := fun _ ↦ 0
  exponent := ![0, 1, 7, 8, 2, 9, 3, 10, 4, 11, 5, 6]
  point_eq := by decide +kernel

def row152Witness : LiteralCyclicOrbitWitness Row152Top 1 where
  element := closureGenerators row152Generators 1 * closureGenerators row152Generators 2 *
    closureGenerators row152Generators 3
  representative := ![0]
  orbitIndex := fun _ ↦ 0
  exponent := ![0, 3, 9, 7, 1, 10, 4, 5, 11, 8, 2, 6]
  point_eq := by decide +kernel

def row153Witness : LiteralCyclicOrbitWitness Row153Top 1 where
  element := closureGenerators row153Generators 1 * closureGenerators row153Generators 3 *
    (closureGenerators row153Generators 2) ^ 2
  representative := ![0]
  orbitIndex := fun _ ↦ 0
  exponent := ![0, 3, 9, 4, 10, 1, 7, 11, 5, 2, 8, 6]
  point_eq := by decide +kernel

theorem row99Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row99Interface.top (Fin 12)) 1 :=
  row99Witness.uniform _

theorem row104Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row104Interface.top (Fin 12)) 1 :=
  row104Witness.uniform _

theorem row143Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row143Interface.top (Fin 12)) 1 :=
  row143Witness.uniform _

theorem row152Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row152Interface.top (Fin 12)) 1 :=
  row152Witness.uniform _

theorem row153Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row153Interface.top (Fin 12)) 1 :=
  row153Witness.uniform _

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveOddPairCycleWordNaturalFamily

end
