import SymmetricSubgroupAsymptotics.BinaryDoubleFiveCycleAveragePolynomial
import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301

/-! Fourteen original cap-two natural bounds. Five rows contain the same
product of a ternary shift and a commuting involution, with two six-point
orbits. Nine more rows realize three common two-generator polynomial
certificates built from two five-cycles. All conclusions retain the
original literal groups, coordinates, and stored capacity two. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

private def retarget {T S : Subgroup (Equiv.Perm (Fin 12))}
    (C : LiteralCyclicOrbitWitness T 2) (g : S) (hg : g.val = C.element.val) :
    LiteralCyclicOrbitWitness S 2 where
  element := g
  representative := C.representative
  orbitIndex := C.orbitIndex
  exponent := C.exponent
  point_eq x := by rw [hg]; exact C.point_eq x

def row3Witness : LiteralCyclicOrbitWitness Row3Top 2 where
  element := closureGenerators row3Generators 0 * closureGenerators row3Generators 2
  representative := ![0, 1]
  orbitIndex := ![0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0]
  exponent := ![0, 0, 3, 1, 4, 4, 1, 5, 2, 2, 5, 3]
  point_eq := by decide +kernel

def row7Witness : LiteralCyclicOrbitWitness Row7Top 2 :=
  retarget row3Witness
    (closureGenerators row7Generators 1 * closureGenerators row7Generators 2)
    (by decide +kernel)

def row23Witness : LiteralCyclicOrbitWitness Row23Top 2 :=
  retarget row3Witness
    (closureGenerators row23Generators 1 * closureGenerators row23Generators 3)
    (by decide +kernel)

def row24Witness : LiteralCyclicOrbitWitness Row24Top 2 :=
  retarget row3Witness
    (closureGenerators row24Generators 1 * closureGenerators row24Generators 3)
    (by decide +kernel)

def row25Witness : LiteralCyclicOrbitWitness Row25Top 2 :=
  retarget row3Witness
    (closureGenerators row25Generators 1 * closureGenerators row25Generators 2)
    (by decide +kernel)

theorem row3Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row3Interface.top (Fin 12)) 2 :=
  row3Witness.uniform _

theorem row7Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row7Interface.top (Fin 12)) 2 :=
  row7Witness.uniform _

theorem row23Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row23Interface.top (Fin 12)) 2 :=
  row23Witness.uniform _

theorem row24Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row24Interface.top (Fin 12)) 2 :=
  row24Witness.uniform _

theorem row25Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row25Interface.top (Fin 12)) 2 :=
  row25Witness.uniform _

theorem row33Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row33Interface.top (Fin 12)) 2 := by
  apply BinaryDoubleFiveCycleAveragePolynomial.uniform_of_basis 0 _
    (closureGenerators row33Generators 0) (closureGenerators row33Generators 1)
  decide +kernel

theorem row74Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row74Interface.top (Fin 12)) 2 := by
  apply BinaryDoubleFiveCycleAveragePolynomial.uniform_of_basis 1 _
    (closureGenerators row74Generators 0) (closureGenerators row74Generators 1)
  decide +kernel

theorem row75Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row75Interface.top (Fin 12)) 2 := by
  apply BinaryDoubleFiveCycleAveragePolynomial.uniform_of_basis 0 _
    (closureGenerators row75Generators 0) (closureGenerators row75Generators 1)
  decide +kernel

theorem row76Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row76Interface.top (Fin 12)) 2 := by
  apply BinaryDoubleFiveCycleAveragePolynomial.uniform_of_basis 1 _
    (closureGenerators row76Generators 1) (closureGenerators row76Generators 3)
  decide +kernel

theorem row123Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row123Interface.top (Fin 12)) 2 := by
  apply BinaryDoubleFiveCycleAveragePolynomial.uniform_of_basis 0 _
    (closureGenerators row123Generators 0) (closureGenerators row123Generators 1)
  decide +kernel

theorem row183Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row183Interface.top (Fin 12)) 2 := by
  apply BinaryDoubleFiveCycleAveragePolynomial.uniform_of_basis 2 _
    (closureGenerators row183Generators 1) (closureGenerators row183Generators 0)
  decide +kernel

theorem row230Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row230Interface.top (Fin 12)) 2 := by
  apply BinaryDoubleFiveCycleAveragePolynomial.uniform_of_basis 0 _
    (closureGenerators row230Generators 1) (closureGenerators row230Generators 2)
  decide +kernel

theorem row257Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row257Interface.top (Fin 12)) 2 := by
  apply BinaryDoubleFiveCycleAveragePolynomial.uniform_of_basis 0 _
    (closureGenerators row257Generators 1) (closureGenerators row257Generators 2)
  decide +kernel

theorem row277Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row277Interface.top (Fin 12)) 2 := by
  apply BinaryDoubleFiveCycleAveragePolynomial.uniform_of_basis 2 _
    (closureGenerators row277Generators 2) (closureGenerators row277Generators 1)
  decide +kernel

end PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily
end SymmetricSubgroupAsymptotics

end
