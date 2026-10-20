import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow20NaturalModule
import SymmetricSubgroupAsymptotics.PermutationNaturalBoundPointEmbedding
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-! Eight literal natural-module fields share the row20 coefficient-action
proof. Two inclusions use original generators; five use the product of
three explicitly displayed conjugates. Every inclusion is checked on the
twelve original points and retains the source generator tuple. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveRow20NaturalFamily

open DegreeTwoTwelvePairFiniteCatalogue

private def ternaryNorm {G : Type} [Group G] (t c : G) : G :=
  t * (c * t * c⁻¹) * (c ^ 2 * t * (c ^ 2)⁻¹)

theorem row20Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row20Interface.top (Fin 12)) 1 :=
  PrimitiveAffineDegreeTwoTwelveRow20NaturalModule.natural

def row43Embedding : LiteralPermutationGeneratorEmbedding row20Generators Row43Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row43Generators 0, closureGenerators row43Generators 1,
    closureGenerators row43Generators 2]
  point_eq := by decide +kernel

def row44Embedding : LiteralPermutationGeneratorEmbedding row20Generators Row44Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row44Generators 1, closureGenerators row44Generators 2,
    closureGenerators row44Generators 0]
  point_eq := by decide +kernel

def row164Embedding : LiteralPermutationGeneratorEmbedding row20Generators Row164Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row164Generators 2,
    ternaryNorm (closureGenerators row164Generators 1) (closureGenerators row164Generators 3) *
      (closureGenerators row164Generators 2)⁻¹,
    closureGenerators row164Generators 3]
  point_eq := by decide +kernel

def row204Embedding : LiteralPermutationGeneratorEmbedding row20Generators Row204Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row204Generators 2,
    ternaryNorm (closureGenerators row204Generators 1) (closureGenerators row204Generators 3) *
      (closureGenerators row204Generators 2)⁻¹,
    closureGenerators row204Generators 3]
  point_eq := by decide +kernel

def row205Embedding : LiteralPermutationGeneratorEmbedding row20Generators Row205Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row205Generators 2,
    ternaryNorm (closureGenerators row205Generators 1) (closureGenerators row205Generators 4) *
      (closureGenerators row205Generators 2)⁻¹,
    closureGenerators row205Generators 4]
  point_eq := by decide +kernel

def row206Embedding : LiteralPermutationGeneratorEmbedding row20Generators Row206Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row206Generators 2,
    ternaryNorm (closureGenerators row206Generators 1) (closureGenerators row206Generators 3) *
      (closureGenerators row206Generators 2)⁻¹,
    closureGenerators row206Generators 3]
  point_eq := by decide +kernel

def row239Embedding : LiteralPermutationGeneratorEmbedding row20Generators Row239Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row239Generators 2,
    ternaryNorm (closureGenerators row239Generators 1) (closureGenerators row239Generators 4) *
      (closureGenerators row239Generators 2)⁻¹,
    closureGenerators row239Generators 4]
  point_eq := by decide +kernel

theorem row43Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row43Interface.top (Fin 12)) 1 :=
  row43Embedding.uniform row20Natural

theorem row44Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row44Interface.top (Fin 12)) 1 :=
  row44Embedding.uniform row20Natural

theorem row164Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row164Interface.top (Fin 12)) 1 :=
  row164Embedding.uniform row20Natural

theorem row204Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row204Interface.top (Fin 12)) 1 :=
  row204Embedding.uniform row20Natural

theorem row205Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row205Interface.top (Fin 12)) 1 :=
  row205Embedding.uniform row20Natural

theorem row206Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row206Interface.top (Fin 12)) 1 :=
  row206Embedding.uniform row20Natural

theorem row239Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row239Interface.top (Fin 12)) 1 :=
  row239Embedding.uniform row20Natural

end DegreeTwoTwelveRow20NaturalFamily
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
