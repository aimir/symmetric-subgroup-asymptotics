import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow20NaturalModule
import SymmetricSubgroupAsymptotics.PermutationNaturalBoundPointEmbedding
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301

/-! Five exact natural-module bounds from a common diagonal A4 action.
A paired ternary rotation r=(a,a^-1,1) and the three-block cycle c give
the diagonal rotation r*(c*r*c^-1)^2. The norm of a local double
transposition supplies the diagonal Klein action. Two fixed charts bind
these words to the checked row20 A4×C3 module, retaining each target top.
Only natural-module bounds are transported through these embeddings. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveDiagonalAlternatingNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def diagonalRotation {G : Type} [Group G] (r c : G) : G :=
  r * (c * r * c⁻¹) ^ 2

def diagonalInvolution {G : Type} [Group G] (k c : G) : G :=
  k * (c * k * c⁻¹) * (c ^ 2 * k * (c ^ 2)⁻¹)

def diagonalGenerators {G : Type} [Group G] (k r c : G) : Fin 3 → G :=
  ![diagonalRotation r c, diagonalInvolution k c * (diagonalRotation r c)⁻¹, c]

def firstChart : Fin 12 ≃ Fin 12 where
  toFun := ![8, 3, 1, 2, 0, 7, 5, 6, 4, 11, 9, 10]
  invFun := ![4, 2, 3, 1, 8, 6, 7, 5, 0, 10, 11, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def secondChart : Fin 12 ≃ Fin 12 where
  toFun := ![11, 9, 10, 8, 3, 1, 2, 0, 7, 5, 6, 4]
  invFun := ![7, 5, 6, 4, 11, 9, 10, 8, 3, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row229Embedding : LiteralPermutationGeneratorEmbedding row20Generators Row229Top where
  pointEquiv := firstChart
  images := diagonalGenerators (closureGenerators row229Generators 0)
    (closureGenerators row229Generators 2) (closureGenerators row229Generators 3)
  point_eq := by decide +kernel

def row251Embedding : LiteralPermutationGeneratorEmbedding row20Generators Row251Top where
  pointEquiv := firstChart
  images := diagonalGenerators (closureGenerators row251Generators 0)
    (closureGenerators row251Generators 2) (closureGenerators row251Generators 3)
  point_eq := by decide +kernel

def row252Embedding : LiteralPermutationGeneratorEmbedding row20Generators Row252Top where
  pointEquiv := firstChart
  images := diagonalGenerators (closureGenerators row252Generators 0)
    (closureGenerators row252Generators 2) (closureGenerators row252Generators 3)
  point_eq := by decide +kernel

def row253Embedding : LiteralPermutationGeneratorEmbedding row20Generators Row253Top where
  pointEquiv := secondChart
  images := diagonalGenerators (closureGenerators row253Generators 0)
    (closureGenerators row253Generators 2) (closureGenerators row253Generators 4)
  point_eq := by decide +kernel

def row268Embedding : LiteralPermutationGeneratorEmbedding row20Generators Row268Top where
  pointEquiv := secondChart
  images := diagonalGenerators (closureGenerators row268Generators 0)
    (closureGenerators row268Generators 2) (closureGenerators row268Generators 4)
  point_eq := by decide +kernel

theorem row229Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row229Interface.top (Fin 12)) 1 :=
  row229Embedding.uniform PrimitiveAffineDegreeTwoTwelveRow20NaturalModule.natural

theorem row251Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row251Interface.top (Fin 12)) 1 :=
  row251Embedding.uniform PrimitiveAffineDegreeTwoTwelveRow20NaturalModule.natural

theorem row252Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row252Interface.top (Fin 12)) 1 :=
  row252Embedding.uniform PrimitiveAffineDegreeTwoTwelveRow20NaturalModule.natural

theorem row253Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row253Interface.top (Fin 12)) 1 :=
  row253Embedding.uniform PrimitiveAffineDegreeTwoTwelveRow20NaturalModule.natural

theorem row268Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row268Interface.top (Fin 12)) 1 :=
  row268Embedding.uniform PrimitiveAffineDegreeTwoTwelveRow20NaturalModule.natural

end PrimitiveAffineDegreeTwoTwelveDiagonalAlternatingNaturalFamily
end SymmetricSubgroupAsymptotics

end
