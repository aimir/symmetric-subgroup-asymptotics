import SymmetricSubgroupAsymptotics.BinaryFourTernaryCycleOperator
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301

/-! Twelve original capacity-one natural fields on four ternary blocks.
The actual block movers may have reflection monodromy. The common algebra
operator retains their constant action and replaces the final augmentation
transfer by a local ternary rotation. Each displayed point chart and every
basis step is checked directly on the original retained generator tuple. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveTernaryBlockCycleNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def pointCycle (j : Fin 8) : Equiv.Perm (Fin 12) where
  toFun x := ((#[
    #[0, 3, 1, 10, 4, 7, 9, 6, 8, 11, 5, 2],
    #[3, 6, 9, 4, 7, 10, 1, 0, 11, 2, 5, 8],
    #[3, 6, 0, 1, 7, 10, 8, 9, 11, 2, 4, 5],
    #[3, 2, 1, 8, 7, 10, 9, 4, 11, 6, 5, 0],
    #[3, 9, 0, 6, 7, 1, 8, 10, 11, 5, 4, 2],
    #[3, 6, 9, 8, 7, 10, 1, 4, 11, 2, 5, 0],
    #[3, 10, 9, 4, 7, 6, 1, 0, 11, 2, 5, 8],
    #[3, 4, 1, 2, 7, 8, 9, 10, 11, 0, 5, 6]
    ] : Array (Array (Fin 12)))[j.val]!)[x.val]!
  invFun x := ((#[
    #[0, 2, 11, 1, 4, 10, 7, 5, 8, 6, 3, 9],
    #[7, 6, 9, 0, 3, 10, 1, 4, 11, 2, 5, 8],
    #[2, 3, 9, 0, 10, 11, 1, 4, 6, 7, 5, 8],
    #[11, 2, 1, 0, 7, 10, 9, 4, 3, 6, 5, 8],
    #[2, 5, 11, 0, 10, 9, 3, 4, 6, 1, 7, 8],
    #[11, 6, 9, 0, 7, 10, 1, 4, 3, 2, 5, 8],
    #[7, 6, 9, 0, 3, 10, 5, 4, 11, 2, 1, 8],
    #[9, 2, 3, 0, 1, 10, 11, 4, 5, 6, 7, 8]
    ] : Array (Array (Fin 12)))[j.val]!)[x.val]!
  left_inv := by revert j; decide +kernel
  right_inv := by revert j; decide +kernel

theorem row46Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row46Interface.top (Fin 12)) 1 := by
  apply BinaryFourTernaryCycleOperator.uniform_of_pointCycle false _
    (closureGenerators row46Generators 0) (closureGenerators row46Generators 2) (pointCycle 0)
  decide +kernel

theorem row84Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row84Interface.top (Fin 12)) 1 := by
  apply BinaryFourTernaryCycleOperator.uniform_of_pointCycle false _
    (closureGenerators row84Generators 0) (closureGenerators row84Generators 2) (pointCycle 0)
  decide +kernel

theorem row157Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row157Interface.top (Fin 12)) 1 := by
  apply BinaryFourTernaryCycleOperator.uniform_of_pointCycle false _
    (closureGenerators row157Generators 0) (closureGenerators row157Generators 2) (pointCycle 0)
  decide +kernel

theorem row173Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row173Interface.top (Fin 12)) 1 := by
  apply BinaryFourTernaryCycleOperator.uniform_of_pointCycle true _
    (closureGenerators row173Generators 0) (closureGenerators row173Generators 2) (pointCycle 1)
  decide +kernel

theorem row212Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row212Interface.top (Fin 12)) 1 := by
  apply BinaryFourTernaryCycleOperator.uniform_of_pointCycle true _
    (closureGenerators row212Generators 0)
    (closureGenerators row212Generators 2 * closureGenerators row212Generators 3) (pointCycle 2)
  decide +kernel

theorem row215Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row215Interface.top (Fin 12)) 1 := by
  apply BinaryFourTernaryCycleOperator.uniform_of_pointCycle true _
    (closureGenerators row215Generators 0) (closureGenerators row215Generators 3) (pointCycle 3)
  decide +kernel

theorem row216Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row216Interface.top (Fin 12)) 1 := by
  apply BinaryFourTernaryCycleOperator.uniform_of_pointCycle true _
    (closureGenerators row216Generators 0)
    (closureGenerators row216Generators 2 * closureGenerators row216Generators 3) (pointCycle 4)
  decide +kernel

theorem row243Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row243Interface.top (Fin 12)) 1 := by
  apply BinaryFourTernaryCycleOperator.uniform_of_pointCycle true _
    (closureGenerators row243Generators 0)
    (closureGenerators row243Generators 2 * closureGenerators row243Generators 3) (pointCycle 5)
  decide +kernel

theorem row244Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row244Interface.top (Fin 12)) 1 := by
  apply BinaryFourTernaryCycleOperator.uniform_of_pointCycle true _
    (closureGenerators row244Generators 0) (closureGenerators row244Generators 3) (pointCycle 6)
  decide +kernel

theorem row249Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row249Interface.top (Fin 12)) 1 := by
  apply BinaryFourTernaryCycleOperator.uniform_of_pointCycle true _
    (closureGenerators row249Generators 0)
    (closureGenerators row249Generators 2 * closureGenerators row249Generators 3) (pointCycle 7)
  decide +kernel

theorem row262Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row262Interface.top (Fin 12)) 1 := by
  apply BinaryFourTernaryCycleOperator.uniform_of_pointCycle true _
    (closureGenerators row262Generators 0) (closureGenerators row262Generators 4) (pointCycle 6)
  decide +kernel

theorem row266Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row266Interface.top (Fin 12)) 1 := by
  apply BinaryFourTernaryCycleOperator.uniform_of_pointCycle true _
    (closureGenerators row266Generators 0)
    (closureGenerators row266Generators 2 * closureGenerators row266Generators 4) (pointCycle 6)
  decide +kernel

end PrimitiveAffineDegreeTwoTwelveTernaryBlockCycleNaturalFamily
end SymmetricSubgroupAsymptotics

end
