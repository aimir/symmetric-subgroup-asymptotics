import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow133NaturalModule
import SymmetricSubgroupAsymptotics.PermutationNaturalBoundPointEmbedding
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-! Three exact embeddings of the augmentation/A4 root action. The
single-block translation in rows194 and234 supplies the root translation
as the product of its first three block conjugates. Only natural-module
bounds, not quotient-socle statements, are transported by these maps. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow133NaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def row176Embedding : LiteralPermutationGeneratorEmbedding row133Generators Row176Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row176Generators 0, closureGenerators row176Generators 2,
    closureGenerators row176Generators 3]
  point_eq := by decide +kernel

def row194Translation : Row194Top :=
  let t := closureGenerators row194Generators 0
  let s := closureGenerators row194Generators 1
  t * (s * t * s⁻¹) * (s ^ 2 * t * (s ^ 2)⁻¹)

def row194Embedding : LiteralPermutationGeneratorEmbedding row133Generators Row194Top where
  pointEquiv := Equiv.refl _
  images := ![row194Translation, closureGenerators row194Generators 1,
    closureGenerators row194Generators 2]
  point_eq := by decide +kernel

def row234Translation : Row234Top :=
  let t := closureGenerators row234Generators 0
  let s := closureGenerators row234Generators 2
  t * (s * t * s⁻¹) * (s ^ 2 * t * (s ^ 2)⁻¹)

def row234Embedding : LiteralPermutationGeneratorEmbedding row133Generators Row234Top where
  pointEquiv := Equiv.refl _
  images := ![row234Translation, closureGenerators row234Generators 2,
    closureGenerators row234Generators 3]
  point_eq := by decide +kernel

theorem row133Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row133Interface.top (Fin 12)) 1 :=
  PrimitiveAffineDegreeTwoTwelveRow133NaturalModule.natural

theorem row176Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row176Interface.top (Fin 12)) 1 :=
  row176Embedding.uniform row133Natural

theorem row194Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row194Interface.top (Fin 12)) 1 :=
  row194Embedding.uniform row133Natural

theorem row234Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row234Interface.top (Fin 12)) 1 :=
  row234Embedding.uniform row133Natural

end PrimitiveAffineDegreeTwoTwelveRow133NaturalFamily
end SymmetricSubgroupAsymptotics

end
