import SymmetricSubgroupAsymptotics.BinaryPairedTernaryCentralFlipPolynomial
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100

/-! Original rows41/78 realize the same paired ternary/central flip
construction. Both retain their exact natural capacity one. Row78
reconstructs the local ternary rotation from its two listed six-cycles. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedTernaryCentralFlipNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def row78Chart : Equiv.Perm (Fin 12) where
  toFun := ![0, 6, 5, 3, 4, 2, 1, 7, 8, 10, 9, 11]
  invFun := ![0, 6, 5, 3, 4, 2, 1, 7, 8, 10, 9, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem row41Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row41Interface.top (Fin 12)) 1 := by
  apply BinaryPairedTernaryCentralFlipPolynomial.uniform_of_basis _
    (closureGenerators row41Generators 1) (closureGenerators row41Generators 0)
    (closureGenerators row41Generators 3) (Equiv.refl _)
  decide +kernel

theorem row78Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row78Interface.top (Fin 12)) 1 := by
  let a := closureGenerators row78Generators 1
  let b := closureGenerators row78Generators 2
  apply BinaryPairedTernaryCentralFlipPolynomial.uniform_of_basis _
    ((a ^ 2 * b ^ 2) ^ 2) (closureGenerators row78Generators 0)
    (a * closureGenerators row78Generators 3) row78Chart
  decide +kernel

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedTernaryCentralFlipNaturalFamily

end
