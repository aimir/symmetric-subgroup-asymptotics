import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.PermutationNaturalBoundPointEmbedding
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50

/-! The central involution adjoining the original row4 action gives a
two-orbit cyclic witness in row6. Row26 contains the same literal tuple,
so the shared cyclic-orbit/PID theorem gives both stored cap-two fields. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveCentralInvolutionNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def row6Witness : LiteralCyclicOrbitWitness Row6Top 2 where
  element := closureGenerators row6Generators 0 * closureGenerators row6Generators 2
  representative := ![0, 1]
  orbitIndex := ![0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1]
  exponent := ![0, 0, 2, 4, 2, 1, 3, 5, 4, 1, 3, 5]
  point_eq := by decide +kernel

theorem row6Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row6Interface.top (Fin 12)) 2 :=
  row6Witness.uniform _

def row26Embedding : LiteralPermutationGeneratorEmbedding row6Generators Row26Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row26Generators 0, closureGenerators row26Generators 1,
    closureGenerators row26Generators 2]
  point_eq := by decide +kernel

theorem row26Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row26Interface.top (Fin 12)) 2 :=
  row26Embedding.uniform row6Natural

end PrimitiveAffineDegreeTwoTwelveCentralInvolutionNaturalFamily
end SymmetricSubgroupAsymptotics

end
