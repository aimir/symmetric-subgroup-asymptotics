import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100

/-! Four explicit cap-three bounds on original actions whose historical
natural capacity is two. They are usable only in a separately proved
admissible alternate profile, such as (1,3). The literal cyclic/PID theorem
is shared; no equality with a historical capacity is asserted. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeOrbitNaturalBounds

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def row59Witness : LiteralCyclicOrbitWitness Row59Top 3 where
  element := closureGenerators row59Generators 1 * closureGenerators row59Generators 3
  representative := ![0, 1, 4]
  orbitIndex := ![0, 1, 1, 0, 2, 1, 1, 0, 2, 1, 1, 2]
  exponent := ![0, 0, 3, 1, 0, 1, 4, 2, 1, 2, 5, 2]
  point_eq := by decide +kernel

def row61Witness : LiteralCyclicOrbitWitness Row61Top 3 where
  element := closureGenerators row61Generators 1 * closureGenerators row61Generators 2
  representative := row59Witness.representative
  orbitIndex := row59Witness.orbitIndex
  exponent := row59Witness.exponent
  point_eq x := by
    have h : ((closureGenerators row61Generators 1 * closureGenerators row61Generators 2 :
        Row61Top) : Equiv.Perm (Fin 12)) = row59Witness.element.val := by decide +kernel
    rw [h]
    exact row59Witness.point_eq x

def row64Witness : LiteralCyclicOrbitWitness Row64Top 3 where
  element := closureGenerators row64Generators 1 * closureGenerators row64Generators 2
  representative := ![0, 1, 6]
  orbitIndex := ![0, 1, 1, 1, 1, 0, 2, 1, 1, 1, 1, 2]
  exponent := ![0, 0, 4, 5, 1, 1, 0, 2, 6, 7, 3, 1]
  point_eq := by decide +kernel

def row66Witness : LiteralCyclicOrbitWitness Row66Top 3 where
  element := closureGenerators row66Generators 1 * closureGenerators row66Generators 3
  representative := ![0, 1, 3]
  orbitIndex := ![0, 1, 1, 2, 0, 2, 0, 1, 1, 0, 2, 2]
  exponent := ![0, 0, 2, 0, 1, 1, 2, 1, 3, 3, 2, 3]
  point_eq := by decide +kernel

theorem row59NaturalThree : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row59Interface.top (Fin 12)) 3 :=
  row59Witness.uniform _

theorem row61NaturalThree : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row61Interface.top (Fin 12)) 3 :=
  row61Witness.uniform _

theorem row64NaturalThree : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row64Interface.top (Fin 12)) 3 :=
  row64Witness.uniform _

theorem row66NaturalThree : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row66Interface.top (Fin 12)) 3 :=
  row66Witness.uniform _

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeOrbitNaturalBounds

end
