import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow5NaturalFamily
import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-! Eight original quartet fields inherit capacity one from two roots.
In row51 a diagonal four-cycle followed by the block three-cycle is a
twelve-cycle. Row142 reconstructs its diagonal double transposition by
the product of three conjugate local flips. Row52 contains the exact
row5 tuple with the rotation written as a product of two involutions. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveQuartetWordNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def row51Witness : LiteralCyclicOrbitWitness Row51Top 1 where
  element := closureGenerators row51Generators 1 * closureGenerators row51Generators 2 *
    closureGenerators row51Generators 3
  representative := fun _ ↦ 0
  orbitIndex := fun _ ↦ 0
  exponent := ![0, 7, 2, 9, 4, 11, 6, 1, 8, 3, 10, 5]
  point_eq := by decide +kernel

theorem row51Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row51Interface.top (Fin 12)) 1 :=
  row51Witness.uniform _

def row86Embedding : LiteralPermutationGeneratorEmbedding row51Generators Row86Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row86Generators 0, closureGenerators row86Generators 1,
    closureGenerators row86Generators 2, closureGenerators row86Generators 3]
  point_eq := by decide +kernel

def diagonalKlein {G : Type} [Group G] (k c : G) : G :=
  k * (c * k * c ^ 2) * (c ^ 2 * k * c)

def row142Embedding : LiteralPermutationGeneratorEmbedding row51Generators Row142Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row142Generators 1,
    diagonalKlein (closureGenerators row142Generators 0) (closureGenerators row142Generators 3),
    closureGenerators row142Generators 2, closureGenerators row142Generators 3]
  point_eq := by decide +kernel

def row186Embedding : LiteralPermutationGeneratorEmbedding row142Generators Row186Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row186Generators 0, closureGenerators row186Generators 1,
    closureGenerators row186Generators 2, closureGenerators row186Generators 3]
  point_eq := by decide +kernel

theorem row86Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row86Interface.top (Fin 12)) 1 :=
  row86Embedding.uniform row51Natural

theorem row142Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row142Interface.top (Fin 12)) 1 :=
  row142Embedding.uniform row51Natural

theorem row186Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row186Interface.top (Fin 12)) 1 :=
  row186Embedding.uniform row142Natural

def row52Rotation : Row52Top :=
  closureGenerators row52Generators 1 * closureGenerators row52Generators 3

def row50Rotation : Row50Top :=
  closureGenerators row50Generators 3 * closureGenerators row50Generators 1

def row148Rotation : Row148Top :=
  diagonalKlein (closureGenerators row148Generators 0) (closureGenerators row148Generators 1) *
    closureGenerators row148Generators 2

def row50Embedding : LiteralPermutationGeneratorEmbedding row5Generators Row50Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row50Generators 2, row50Rotation ^ 2, row50Rotation]
  point_eq := by decide +kernel

def row52Embedding : LiteralPermutationGeneratorEmbedding row5Generators Row52Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row52Generators 2, row52Rotation ^ 2, row52Rotation]
  point_eq := by decide +kernel

def row148Embedding : LiteralPermutationGeneratorEmbedding row5Generators Row148Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row148Generators 1, row148Rotation ^ 2, row148Rotation]
  point_eq := by decide +kernel

def row223Embedding : LiteralPermutationGeneratorEmbedding row148Generators Row223Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row223Generators 0, closureGenerators row223Generators 3,
    closureGenerators row223Generators 4]
  point_eq := by decide +kernel

theorem row50Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row50Interface.top (Fin 12)) 1 :=
  row50Embedding.uniform PrimitiveAffineDegreeTwoTwelveRow5NaturalFamily.row5Natural

theorem row52Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row52Interface.top (Fin 12)) 1 :=
  row52Embedding.uniform PrimitiveAffineDegreeTwoTwelveRow5NaturalFamily.row5Natural

theorem row148Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row148Interface.top (Fin 12)) 1 :=
  row148Embedding.uniform PrimitiveAffineDegreeTwoTwelveRow5NaturalFamily.row5Natural

theorem row223Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row223Interface.top (Fin 12)) 1 :=
  row223Embedding.uniform row148Natural

end PrimitiveAffineDegreeTwoTwelveQuartetWordNaturalFamily
end SymmetricSubgroupAsymptotics

end
