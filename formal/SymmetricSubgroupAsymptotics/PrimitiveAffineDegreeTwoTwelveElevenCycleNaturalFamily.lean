import SymmetricSubgroupAsymptotics.BinaryElevenCyclePolynomial
import SymmetricSubgroupAsymptotics.PermutationNaturalBoundPointEmbedding
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-! The original row179 eleven-cycle and mover realize the shared
odd-cycle polynomial operator. Row218 contains their exact original tuple.
Both natural fields retain their stored capacity one. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveElevenCycleNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def pointChart : Equiv.Perm (Fin 12) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 10]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem row179Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row179Interface.top (Fin 12)) 1 := by
  apply BinaryElevenCyclePolynomial.uniform_of_basis _
    (closureGenerators row179Generators 0) (closureGenerators row179Generators 1) pointChart
  decide +kernel

def row218Embedding : LiteralPermutationGeneratorEmbedding row179Generators Row218Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row218Generators 0, closureGenerators row218Generators 1]
  point_eq := by decide +kernel

theorem row218Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row218Interface.top (Fin 12)) 1 :=
  row218Embedding.uniform row179Natural

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveElevenCycleNaturalFamily

end
