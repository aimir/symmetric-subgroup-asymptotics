import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow5NaturalModule
import SymmetricSubgroupAsymptotics.PermutationNaturalBoundPointEmbedding

/-! The row5 module theorem also applies to the two original signed
dihedral tops containing its exact constant translation and signed
rotation. The rotation is the displayed product of two reflections. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow5NaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def row13Embedding : LiteralPermutationGeneratorEmbedding row5Generators Row13Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row13Generators 0, closureGenerators row13Generators 2,
    closureGenerators row13Generators 1 * (closureGenerators row13Generators 3)⁻¹]
  point_eq := by decide +kernel

def row15Embedding : LiteralPermutationGeneratorEmbedding row5Generators Row15Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row15Generators 0,
    closureGenerators row15Generators 1 * (closureGenerators row15Generators 2)⁻¹,
    closureGenerators row15Generators 3 * (closureGenerators row15Generators 2)⁻¹]
  point_eq := by decide +kernel

theorem row5Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row5Interface.top (Fin 12)) 1 :=
  PrimitiveAffineDegreeTwoTwelveRow5NaturalModule.natural

theorem row13Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row13Interface.top (Fin 12)) 1 :=
  row13Embedding.uniform row5Natural

theorem row15Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row15Interface.top (Fin 12)) 1 :=
  row15Embedding.uniform row5Natural

end PrimitiveAffineDegreeTwoTwelveRow5NaturalFamily
end SymmetricSubgroupAsymptotics

end
