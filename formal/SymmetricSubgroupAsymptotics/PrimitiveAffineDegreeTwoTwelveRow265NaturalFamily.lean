import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow265AlgebraPolynomial
import SymmetricSubgroupAsymptotics.PermutationNaturalBoundPointEmbedding

/-! The local alternating four-point action and three-block cycle of
row265 occur unchanged in seven further original tuples. The cyclic
group-algebra operator therefore supplies all eight natural fields. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveRow265NaturalFamily

open DegreeTwoTwelvePairFiniteCatalogue

theorem row265Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row265Interface.top (Fin 12)) 1 :=
  PrimitiveAffineDegreeTwoTwelveRow265AlgebraPolynomial.natural

def row273Embedding : LiteralPermutationGeneratorEmbedding row265Generators Row273Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row273Generators 0, closureGenerators row273Generators 1,
    closureGenerators row273Generators 3]
  point_eq := by decide +kernel

def row275Embedding : LiteralPermutationGeneratorEmbedding row265Generators Row275Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row275Generators 0, closureGenerators row275Generators 1,
    closureGenerators row275Generators 2]
  point_eq := by decide +kernel

def row276Embedding : LiteralPermutationGeneratorEmbedding row265Generators Row276Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row276Generators 0, closureGenerators row276Generators 1,
    closureGenerators row276Generators 2]
  point_eq := by decide +kernel

def row283Embedding : LiteralPermutationGeneratorEmbedding row265Generators Row283Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row283Generators 0, closureGenerators row283Generators 1,
    closureGenerators row283Generators 3]
  point_eq := by decide +kernel

def row284Embedding : LiteralPermutationGeneratorEmbedding row265Generators Row284Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row284Generators 0, closureGenerators row284Generators 1,
    closureGenerators row284Generators 3]
  point_eq := by decide +kernel

def row290Embedding : LiteralPermutationGeneratorEmbedding row265Generators Row290Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row290Generators 0, closureGenerators row290Generators 1,
    closureGenerators row290Generators 3]
  point_eq := by decide +kernel

def row291Embedding : LiteralPermutationGeneratorEmbedding row265Generators Row291Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row291Generators 0, closureGenerators row291Generators 1,
    closureGenerators row291Generators 3]
  point_eq := by decide +kernel

theorem row273Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row273Interface.top (Fin 12)) 1 :=
  row273Embedding.uniform row265Natural

theorem row275Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row275Interface.top (Fin 12)) 1 :=
  row275Embedding.uniform row265Natural

theorem row276Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row276Interface.top (Fin 12)) 1 :=
  row276Embedding.uniform row265Natural

theorem row283Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row283Interface.top (Fin 12)) 1 :=
  row283Embedding.uniform row265Natural

theorem row284Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row284Interface.top (Fin 12)) 1 :=
  row284Embedding.uniform row265Natural

theorem row290Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row290Interface.top (Fin 12)) 1 :=
  row290Embedding.uniform row265Natural

theorem row291Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row291Interface.top (Fin 12)) 1 :=
  row291Embedding.uniform row265Natural

end DegreeTwoTwelveRow265NaturalFamily
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
