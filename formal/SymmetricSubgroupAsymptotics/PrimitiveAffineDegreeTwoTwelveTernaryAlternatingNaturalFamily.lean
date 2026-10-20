import SymmetricSubgroupAsymptotics.BinaryFourTernaryAlternatingOperator
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301

/-! Three alternating-block realizations of one cyclic algebra matrix,
and one additional realization of the four-block-cycle template.
All four conclusions retain the original natural module and stored cap1. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveTernaryAlternatingNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def pointChart (j : Fin 3) : Equiv.Perm (Fin 12) where
  toFun x := ((#[
    #[0, 6, 1, 3, 8, 2, 5, 7, 4, 10, 9, 11],
    #[0, 6, 9, 3, 4, 10, 1, 7, 8, 2, 5, 11],
    #[3, 10, 9, 0, 7, 6, 1, 4, 11, 2, 5, 8]
    ] : Array (Array (Fin 12)))[j.val]!)[x.val]!
  invFun x := ((#[
    #[0, 2, 5, 3, 8, 6, 1, 7, 4, 10, 9, 11],
    #[0, 6, 9, 3, 4, 10, 1, 7, 8, 2, 5, 11],
    #[3, 6, 9, 0, 7, 10, 5, 4, 11, 2, 1, 8]
    ] : Array (Array (Fin 12)))[j.val]!)[x.val]!
  left_inv := by revert j; decide +kernel
  right_inv := by revert j; decide +kernel

def row122a : Row122Top := closureGenerators row122Generators 3
def row122d : Row122Top := row122a * (closureGenerators row122Generators 2)⁻¹
def row122Transports : Fin 4 → Row122Top := ![1, row122a, row122a ^ 2, row122d * row122a ^ 2]

def row132a : Row132Top := closureGenerators row132Generators 3
def row132d : Row132Top := closureGenerators row132Generators 1
def row132Transports : Fin 4 → Row132Top := ![1, row132a, row132a ^ 2, row132d * row132a]

def row232a : Row232Top := closureGenerators row232Generators 3
def row232d : Row232Top := row232a * closureGenerators row232Generators 2
def row232Transports : Fin 4 → Row232Top := ![1, row232a, row232a ^ 2, row232d * row232a ^ 2]

theorem row122Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row122Interface.top (Fin 12)) 1 := by
  apply BinaryFourTernaryAlternatingOperator.uniform_of_basis false _
    (closureGenerators row122Generators 0) row122a row122d row122Transports (pointChart 0)
  decide +kernel

theorem row132Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row132Interface.top (Fin 12)) 1 := by
  apply BinaryFourTernaryAlternatingOperator.uniform_of_basis false _
    (closureGenerators row132Generators 0) row132a row132d row132Transports (pointChart 1)
  decide +kernel

theorem row232Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row232Interface.top (Fin 12)) 1 := by
  apply BinaryFourTernaryAlternatingOperator.uniform_of_basis true _
    (closureGenerators row232Generators 0) row232a row232d row232Transports (pointChart 2)
  decide +kernel

def row259PointCycle : Equiv.Perm (Fin 12) where
  toFun := ![3, 9, 8, 2, 7, 1, 4, 10, 11, 5, 0, 6]
  invFun := ![10, 5, 3, 0, 6, 9, 11, 4, 2, 1, 7, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem row259Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row259Interface.top (Fin 12)) 1 := by
  apply BinaryFourTernaryCycleOperator.uniform_of_pointCycle true _
    (closureGenerators row259Generators 0)
    (closureGenerators row259Generators 2 * closureGenerators row259Generators 3) row259PointCycle
  decide +kernel

end PrimitiveAffineDegreeTwoTwelveTernaryAlternatingNaturalFamily
end SymmetricSubgroupAsymptotics

end
