import SymmetricSubgroupAsymptotics.BinaryTwoTernaryMatrixBlocks
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-! Original row201, zero-based index200, is the selected literal pilot
for the shared two-ternary matrix-block theorem. Three original elements
supply its displayed operator identities on twelve coordinate vectors.
The resulting natural capacity one is the unchanged historical capacity. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwoTernaryMatrixNaturalPilot

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue BinaryTwoTernaryMatrixBlocks

def row201Rotation : Row201Top := closureGenerators row201Generators 3
def row201Exchange : Row201Top := closureGenerators row201Generators 2
def row201Reflection : Row201Top := closureGenerators row201Generators 4

theorem row201Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row201Interface.top (Fin 12)) 1 := by
  apply uniform_of_basis _ row201Rotation row201Exchange row201Reflection
  · intro i
    fin_cases i <;> intro r t <;> fin_cases r <;> fin_cases t <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwoTernaryMatrixNaturalPilot

end
