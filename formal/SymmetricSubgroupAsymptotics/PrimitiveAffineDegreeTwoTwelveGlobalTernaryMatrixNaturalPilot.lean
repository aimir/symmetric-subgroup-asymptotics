import SymmetricSubgroupAsymptotics.BinaryGlobalTernaryMatrixBlocks
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100

/-! Original row54 (index53) is the selected global-ternary matrix pilot.
All operators are explicit words in its original twelve-point generators.
The resulting natural capacity one retains its historical natural capacity. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveGlobalTernaryMatrixNaturalPilot

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue BinaryGlobalTernaryMatrixBlocks

def row54K : Row54Top := closureGenerators row54Generators 0
def row54Rotation : Row54Top := closureGenerators row54Generators 1
def row54Reflection : Row54Top := row54K * closureGenerators row54Generators 2
def row54Exchange : Row54Top := closureGenerators row54Generators 3
def row54GlobalFlip : Row54Top :=
  row54K * (row54Rotation * row54K * row54Rotation⁻¹) *
    (row54Rotation ^ 2 * row54K * (row54Rotation ^ 2)⁻¹)

theorem row54Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row54Interface.top (Fin 12)) 1 := by
  apply uniform_of_basis _ row54Rotation row54Reflection row54Exchange row54GlobalFlip
  · intro i
    fin_cases i <;> intro r t <;> fin_cases r <;> fin_cases t <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveGlobalTernaryMatrixNaturalPilot

end
