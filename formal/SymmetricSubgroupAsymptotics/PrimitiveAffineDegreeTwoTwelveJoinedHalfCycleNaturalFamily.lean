import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301

/-! A local transposition joins the two ternary cycles on one half into
a six-cycle. Following it by the half-swap gives one twelve-cycle. Two
original actions realize exactly the same permutation and exponent table,
so the shared cyclic-orbit/PID theorem retains their natural capacity one. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJoinedHalfCycleNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def row208Witness : LiteralCyclicOrbitWitness Row208Top 1 where
  element := closureGenerators row208Generators 0 * closureGenerators row208Generators 1 *
    closureGenerators row208Generators 2
  representative := fun _ ↦ 0
  orbitIndex := fun _ ↦ 0
  exponent := ![0, 9, 10, 1, 2, 5, 6, 3, 4, 7, 8, 11]
  point_eq := by decide +kernel

def row260Witness : LiteralCyclicOrbitWitness Row260Top 1 where
  element := closureGenerators row260Generators 0 * closureGenerators row260Generators 1 *
    closureGenerators row260Generators 3
  representative := row208Witness.representative
  orbitIndex := row208Witness.orbitIndex
  exponent := row208Witness.exponent
  point_eq := by decide +kernel

theorem row208Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row208Interface.top (Fin 12)) 1 :=
  row208Witness.uniform _

theorem row260Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row260Interface.top (Fin 12)) 1 :=
  row260Witness.uniform _

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJoinedHalfCycleNaturalFamily

end
