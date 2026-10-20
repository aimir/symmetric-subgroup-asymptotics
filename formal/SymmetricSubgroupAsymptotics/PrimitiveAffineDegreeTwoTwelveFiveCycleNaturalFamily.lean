import SymmetricSubgroupAsymptotics.BinaryFiveCycleAveragePolynomial
import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301

/-! Ten original natural-module capacities from six-point-block actions.
Nine cap-one rows realize the shared five-cycle-average polynomial
operator. Each identity is checked only on the twelve coordinate basis
vectors. Row180 has the displayed two-orbit cover at its stored cap two.
Every theorem keeps the original literal top and its original points. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveFiveCycleNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def row180Witness : LiteralCyclicOrbitWitness Row180Top 2 where
  element := closureGenerators row180Generators 1 * closureGenerators row180Generators 2
  representative := ![0, 1]
  orbitIndex := ![0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0]
  exponent := ![0, 0, 5, 6, 1, 2, 7, 8, 3, 4, 9, 1]
  point_eq := by decide +kernel

theorem row180Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row180Interface.top (Fin 12)) 2 :=
  row180Witness.uniform _

theorem row182Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row182Interface.top (Fin 12)) 1 := by
  apply BinaryFiveCycleAveragePolynomial.uniform_of_basis 5 _
    (closureGenerators row182Generators 1) (closureGenerators row182Generators 0)
    (closureGenerators row182Generators 2)
  decide +kernel

theorem row269Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row269Interface.top (Fin 12)) 1 := by
  apply BinaryFiveCycleAveragePolynomial.uniform_of_basis 0 _
    (closureGenerators row269Generators 0) (closureGenerators row269Generators 1)
    (closureGenerators row269Generators 2)
  decide +kernel

theorem row278Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row278Interface.top (Fin 12)) 1 := by
  apply BinaryFiveCycleAveragePolynomial.uniform_of_basis 1 _
    (closureGenerators row278Generators 0) (closureGenerators row278Generators 1)
    (closureGenerators row278Generators 2)
  decide +kernel

theorem row279Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row279Interface.top (Fin 12)) 1 := by
  apply BinaryFiveCycleAveragePolynomial.uniform_of_basis 2 _
    (closureGenerators row279Generators 0) (closureGenerators row279Generators 1)
    (closureGenerators row279Generators 2)
  decide +kernel

theorem row288Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row288Interface.top (Fin 12)) 1 := by
  apply BinaryFiveCycleAveragePolynomial.uniform_of_basis 0 _
    (closureGenerators row288Generators 0) (closureGenerators row288Generators 1)
    (closureGenerators row288Generators 2)
  decide +kernel

theorem row296Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row296Interface.top (Fin 12)) 1 := by
  apply BinaryFiveCycleAveragePolynomial.uniform_of_basis 3 _
    (closureGenerators row296Generators 1) (closureGenerators row296Generators 0)
    (closureGenerators row296Generators 2)
  decide +kernel

theorem row297Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row297Interface.top (Fin 12)) 1 := by
  apply BinaryFiveCycleAveragePolynomial.uniform_of_basis 3 _
    (closureGenerators row297Generators 0) (closureGenerators row297Generators 1)
    (closureGenerators row297Generators 3)
  decide +kernel

theorem row298Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row298Interface.top (Fin 12)) 1 := by
  apply BinaryFiveCycleAveragePolynomial.uniform_of_basis 4 _
    (closureGenerators row298Generators 1) (closureGenerators row298Generators 0)
    (closureGenerators row298Generators 3)
  decide +kernel

theorem row299Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row299Interface.top (Fin 12)) 1 := by
  let t := closureGenerators row299Generators 0
  let f := closureGenerators row299Generators 1
  apply BinaryFiveCycleAveragePolynomial.uniform_of_basis 3 _
    (t * f) (t * (f * t * f⁻¹)) (closureGenerators row299Generators 2)
  dsimp only [t, f]
  decide +kernel

end PrimitiveAffineDegreeTwoTwelveFiveCycleNaturalFamily
end SymmetricSubgroupAsymptotics

end
