import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150

/-! Six original cap-two natural bounds from the common polynomial-orbit
template. Each selected translation/involution product has two six-point
orbits. Row130 first adds the opposite translated seed by one conjugate;
its resulting permutation is exactly the row18 witness. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveKleinNaturalWitnesses

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

def row2Witness : LiteralCyclicOrbitWitness Row2Top 2 where
  element := closureGenerators row2Generators 2 * closureGenerators row2Generators 0
  representative := ![0, 2]
  orbitIndex := ![0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1]
  exponent := ![0, 1, 0, 1, 4, 5, 4, 5, 2, 3, 2, 3]
  point_eq := by decide +kernel

def row16Witness : LiteralCyclicOrbitWitness Row16Top 2 where
  element := closureGenerators row16Generators 0 * closureGenerators row16Generators 1
  representative := ![0, 2]
  orbitIndex := ![0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1]
  exponent := ![0, 3, 0, 1, 4, 1, 2, 3, 2, 5, 4, 5]
  point_eq := by decide +kernel

def row18Witness : LiteralCyclicOrbitWitness Row18Top 2 where
  element := closureGenerators row18Generators 0 * closureGenerators row18Generators 1
  representative := ![0, 2]
  orbitIndex := ![0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1]
  exponent := ![0, 1, 0, 1, 2, 3, 2, 3, 4, 5, 4, 5]
  point_eq := by decide +kernel

def row70Witness : LiteralCyclicOrbitWitness Row70Top 2 where
  element := closureGenerators row70Generators 0 * closureGenerators row70Generators 2
  representative := ![0, 1]
  orbitIndex := ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
  exponent := ![0, 0, 3, 5, 2, 4, 5, 3, 4, 2, 1, 1]
  point_eq := by decide +kernel

def row71Witness : LiteralCyclicOrbitWitness Row71Top 2 :=
  retarget row70Witness
    (closureGenerators row71Generators 0 * closureGenerators row71Generators 2)
    (by decide +kernel)

def row130Witness : LiteralCyclicOrbitWitness Row130Top 2 :=
  retarget row18Witness
    ((closureGenerators row130Generators 0 *
      (closureGenerators row130Generators 2 * closureGenerators row130Generators 0 *
        (closureGenerators row130Generators 2)⁻¹)) * closureGenerators row130Generators 1)
    (by decide +kernel)

theorem row2Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row2Interface.top (Fin 12)) 2 :=
  row2Witness.uniform _

theorem row16Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row16Interface.top (Fin 12)) 2 :=
  row16Witness.uniform _

theorem row18Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row18Interface.top (Fin 12)) 2 :=
  row18Witness.uniform _

theorem row70Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row70Interface.top (Fin 12)) 2 :=
  row70Witness.uniform _

theorem row71Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row71Interface.top (Fin 12)) 2 :=
  row71Witness.uniform _

theorem row130Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row130Interface.top (Fin 12)) 2 :=
  row130Witness.uniform _

end PrimitiveAffineDegreeTwoTwelveKleinNaturalWitnesses
end SymmetricSubgroupAsymptotics

end
