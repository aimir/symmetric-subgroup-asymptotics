import SymmetricSubgroupAsymptotics.PermutationNaturalBoundPointEmbedding
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow17NaturalModule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-!
# Nine literal overgroups of the cyclic natural module in row 17

Each certificate displays a point chart and two words in the actual
target generators. The finite checks are the chart inverse identities
and the two generator identities on twelve points. Uniform natural-module
generation transfers through these inclusions; no quotient-socle property
is transferred.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveRow17NaturalFamily

open DegreeTwoTwelvePairFiniteCatalogue

private def chart35 : Fin 12 ≃ Fin 12 where
  toFun := ![4, 1, 10, 3, 8, 9, 6, 7, 0, 5, 2, 11]
  invFun := ![8, 1, 10, 3, 0, 9, 6, 7, 4, 5, 2, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def chart36 : Fin 12 ≃ Fin 12 where
  toFun := ![0, 9, 11, 2, 4, 1, 7, 10, 8, 5, 3, 6]
  invFun := ![0, 5, 3, 10, 4, 9, 11, 6, 8, 1, 7, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def chart73 : Fin 12 ≃ Fin 12 where
  toFun := ![7, 4, 5, 6, 3, 8, 1, 10, 11, 0, 9, 2]
  invFun := ![9, 6, 11, 4, 1, 2, 3, 0, 5, 10, 7, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def chart177 : Fin 12 ≃ Fin 12 where
  toFun := ![2, 8, 1, 3, 10, 0, 9, 7, 6, 4, 5, 11]
  invFun := ![5, 2, 0, 3, 9, 10, 8, 7, 1, 6, 4, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def chart178 : Fin 12 ≃ Fin 12 where
  toFun := ![10, 4, 5, 3, 6, 8, 1, 7, 2, 0, 9, 11]
  invFun := ![9, 6, 8, 3, 1, 2, 4, 7, 5, 10, 0, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- The commutator with the square of the block four-cycle isolates the
two opposite ternary translations used by row 17. -/
private def oppositeTranslation {G : Type} [Group G] (t c : G) : G :=
  t * c ^ 2 * t⁻¹ * (c ^ 2)⁻¹

def row35Embedding : LiteralPermutationGeneratorEmbedding row17Generators Row35Top where
  pointEquiv := chart35
  images := ![closureGenerators row35Generators 0,
    (closureGenerators row35Generators 1 * closureGenerators row35Generators 2) ^ 3]
  point_eq := by decide +kernel

def row36Embedding : LiteralPermutationGeneratorEmbedding row17Generators Row36Top where
  pointEquiv := chart36
  images := ![closureGenerators row36Generators 0 ^ 2 * closureGenerators row36Generators 1 *
      closureGenerators row36Generators 0 ^ 2 * (closureGenerators row36Generators 1)⁻¹,
    (closureGenerators row36Generators 1 * closureGenerators row36Generators 0 ^ 3) ^ 3]
  point_eq := by decide +kernel

def row73Embedding : LiteralPermutationGeneratorEmbedding row17Generators Row73Top where
  pointEquiv := chart73
  images := ![oppositeTranslation (closureGenerators row73Generators 0)
      (closureGenerators row73Generators 2),
    closureGenerators row73Generators 2]
  point_eq := by decide +kernel

def row118Embedding : LiteralPermutationGeneratorEmbedding row17Generators Row118Top where
  pointEquiv := chart73
  images := ![oppositeTranslation (closureGenerators row118Generators 0)
      (closureGenerators row118Generators 1 * closureGenerators row118Generators 3),
    closureGenerators row118Generators 1 * closureGenerators row118Generators 3]
  point_eq := by decide +kernel

def row121Embedding : LiteralPermutationGeneratorEmbedding row17Generators Row121Top where
  pointEquiv := chart73
  images := ![oppositeTranslation (closureGenerators row121Generators 0)
      (closureGenerators row121Generators 1 * closureGenerators row121Generators 3),
    closureGenerators row121Generators 1 * closureGenerators row121Generators 3]
  point_eq := by decide +kernel

def row177Embedding : LiteralPermutationGeneratorEmbedding row17Generators Row177Top where
  pointEquiv := chart177
  images := ![oppositeTranslation (closureGenerators row177Generators 0)
      ((closureGenerators row177Generators 1 * closureGenerators row177Generators 3) ^ 3),
    (closureGenerators row177Generators 1 * closureGenerators row177Generators 3) ^ 3]
  point_eq := by decide +kernel

def row178Embedding : LiteralPermutationGeneratorEmbedding row17Generators Row178Top where
  pointEquiv := chart178
  images := ![oppositeTranslation (closureGenerators row178Generators 0)
      ((closureGenerators row178Generators 1 * closureGenerators row178Generators 3) ^ 3),
    (closureGenerators row178Generators 1 * closureGenerators row178Generators 3) ^ 3]
  point_eq := by decide +kernel

def row200Embedding : LiteralPermutationGeneratorEmbedding row17Generators Row200Top where
  pointEquiv := chart35
  images := ![closureGenerators row200Generators 1,
    ((closureGenerators row200Generators 2 * closureGenerators row200Generators 1 *
      closureGenerators row200Generators 2 * (closureGenerators row200Generators 1)⁻¹ *
      (closureGenerators row200Generators 2)⁻¹) * closureGenerators row200Generators 3) ^ 3]
  point_eq := by decide +kernel

def row233Embedding : LiteralPermutationGeneratorEmbedding row17Generators Row233Top where
  pointEquiv := chart178
  images := ![oppositeTranslation (closureGenerators row233Generators 0)
      ((closureGenerators row233Generators 1 * closureGenerators row233Generators 3) ^ 3),
    (closureGenerators row233Generators 1 * closureGenerators row233Generators 3) ^ 3]
  point_eq := by decide +kernel

theorem row35Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row35Interface.top (Fin 12)) 1 :=
  row35Embedding.uniform PrimitiveAffineDegreeTwoTwelveRow17NaturalModule.natural

theorem row36Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row36Interface.top (Fin 12)) 1 :=
  row36Embedding.uniform PrimitiveAffineDegreeTwoTwelveRow17NaturalModule.natural

theorem row73Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row73Interface.top (Fin 12)) 1 :=
  row73Embedding.uniform PrimitiveAffineDegreeTwoTwelveRow17NaturalModule.natural

theorem row118Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row118Interface.top (Fin 12)) 1 :=
  row118Embedding.uniform PrimitiveAffineDegreeTwoTwelveRow17NaturalModule.natural

theorem row121Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row121Interface.top (Fin 12)) 1 :=
  row121Embedding.uniform PrimitiveAffineDegreeTwoTwelveRow17NaturalModule.natural

theorem row177Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row177Interface.top (Fin 12)) 1 :=
  row177Embedding.uniform PrimitiveAffineDegreeTwoTwelveRow17NaturalModule.natural

theorem row178Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row178Interface.top (Fin 12)) 1 :=
  row178Embedding.uniform PrimitiveAffineDegreeTwoTwelveRow17NaturalModule.natural

theorem row200Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row200Interface.top (Fin 12)) 1 :=
  row200Embedding.uniform PrimitiveAffineDegreeTwoTwelveRow17NaturalModule.natural

theorem row233Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row233Interface.top (Fin 12)) 1 :=
  row233Embedding.uniform PrimitiveAffineDegreeTwoTwelveRow17NaturalModule.natural

end DegreeTwoTwelveRow17NaturalFamily
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
