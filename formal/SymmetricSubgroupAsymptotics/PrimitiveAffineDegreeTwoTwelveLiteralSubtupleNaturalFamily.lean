import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow31NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFiveCycleNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow133NaturalFamily
import SymmetricSubgroupAsymptotics.PermutationNaturalBoundPointEmbedding
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301

/-! Five further natural fields obtained from exact retained generator
subtuples. Every point chart is the identity. The checked root capacities
are preserved: two for row62, one for rows220,271,280,282. No quotient-socle
claim is transported through these acting-group inclusions. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveLiteralSubtupleNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def row62Embedding : LiteralPermutationGeneratorEmbedding row31Generators Row62Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row62Generators 0, closureGenerators row62Generators 1]
  point_eq := by decide +kernel

def row220Embedding : LiteralPermutationGeneratorEmbedding row182Generators Row220Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row220Generators 0, closureGenerators row220Generators 1,
    closureGenerators row220Generators 3]
  point_eq := by decide +kernel

def row271Embedding : LiteralPermutationGeneratorEmbedding row194Generators Row271Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row271Generators 0, closureGenerators row271Generators 2,
    closureGenerators row271Generators 3]
  point_eq := by decide +kernel

def row280Embedding : LiteralPermutationGeneratorEmbedding row194Generators Row280Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row280Generators 0, closureGenerators row280Generators 2,
    closureGenerators row280Generators 3]
  point_eq := by decide +kernel

def row282Embedding : LiteralPermutationGeneratorEmbedding row194Generators Row282Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row282Generators 0, closureGenerators row282Generators 2,
    closureGenerators row282Generators 3]
  point_eq := by decide +kernel

theorem row62Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row62Interface.top (Fin 12)) 2 :=
  row62Embedding.uniform PrimitiveAffineDegreeTwoTwelveRow31NaturalModule.natural

theorem row220Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row220Interface.top (Fin 12)) 1 :=
  row220Embedding.uniform PrimitiveAffineDegreeTwoTwelveFiveCycleNaturalFamily.row182Natural

theorem row271Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row271Interface.top (Fin 12)) 1 :=
  row271Embedding.uniform PrimitiveAffineDegreeTwoTwelveRow133NaturalFamily.row194Natural

theorem row280Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row280Interface.top (Fin 12)) 1 :=
  row280Embedding.uniform PrimitiveAffineDegreeTwoTwelveRow133NaturalFamily.row194Natural

theorem row282Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row282Interface.top (Fin 12)) 1 :=
  row282Embedding.uniform PrimitiveAffineDegreeTwoTwelveRow133NaturalFamily.row194Natural

end PrimitiveAffineDegreeTwoTwelveLiteralSubtupleNaturalFamily
end SymmetricSubgroupAsymptotics

end
