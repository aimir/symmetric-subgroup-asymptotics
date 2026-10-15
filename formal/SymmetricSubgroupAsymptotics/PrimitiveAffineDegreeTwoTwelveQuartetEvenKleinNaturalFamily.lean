import SymmetricSubgroupAsymptotics.BinaryTripleQuartetPolynomial
import SymmetricSubgroupAsymptotics.PermutationNaturalBoundPointEmbedding
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200

/-! Five original capacity-one fields share the same three-quartet
action with an even Klein-four base. The original row85 tuple realizes
the four polynomial-block projectors. Four larger original actions
contain exactly that tuple at the identity point chart. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveQuartetEvenKleinNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

theorem row85Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row85Interface.top (Fin 12)) 1 := by
  apply BinaryTripleQuartetPolynomial.uniform_of_basis _
    (closureGenerators row85Generators 0) (closureGenerators row85Generators 1)
    (closureGenerators row85Generators 2)
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel

def row127Embedding : LiteralPermutationGeneratorEmbedding row85Generators Row127Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row127Generators 0, closureGenerators row127Generators 1,
    closureGenerators row127Generators 2]
  point_eq := by decide +kernel

def row128Embedding : LiteralPermutationGeneratorEmbedding row85Generators Row128Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row128Generators 0, closureGenerators row128Generators 1,
    closureGenerators row128Generators 2]
  point_eq := by decide +kernel

def row129Embedding : LiteralPermutationGeneratorEmbedding row85Generators Row129Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row129Generators 0, closureGenerators row129Generators 1,
    closureGenerators row129Generators 3]
  point_eq := by decide +kernel

def row165Embedding : LiteralPermutationGeneratorEmbedding row85Generators Row165Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row165Generators 0, closureGenerators row165Generators 1,
    closureGenerators row165Generators 3]
  point_eq := by decide +kernel

theorem row127Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row127Interface.top (Fin 12)) 1 :=
  row127Embedding.uniform row85Natural

theorem row128Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row128Interface.top (Fin 12)) 1 :=
  row128Embedding.uniform row85Natural

theorem row129Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row129Interface.top (Fin 12)) 1 :=
  row129Embedding.uniform row85Natural

theorem row165Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row165Interface.top (Fin 12)) 1 :=
  row165Embedding.uniform row85Natural

end PrimitiveAffineDegreeTwoTwelveQuartetEvenKleinNaturalFamily
end SymmetricSubgroupAsymptotics

end
