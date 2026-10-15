import SymmetricSubgroupAsymptotics.BinaryPairedTernaryCentralFlipPolynomial
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100

/-! Two further original cap-one fields realize the same paired ternary
augmentation operator. Products of the displayed movers give four-cycles
on the ternary constants; row82 reconstructs the global central flip from
the flips on the two halves. The natural capacities remain exactly one. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedTernaryFlipWordNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def row80Chart : Equiv.Perm (Fin 12) where
  toFun := ![1, 4, 3, 6, 5, 0, 11, 10, 9, 8, 7, 2]
  invFun := ![5, 0, 11, 2, 1, 4, 3, 10, 9, 8, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row82Chart : Equiv.Perm (Fin 12) where
  toFun := ![0, 2, 1, 3, 4, 6, 5, 7, 8, 10, 9, 11]
  invFun := ![0, 2, 1, 3, 4, 6, 5, 7, 8, 10, 9, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem row80Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row80Interface.top (Fin 12)) 1 := by
  apply BinaryPairedTernaryCentralFlipPolynomial.uniform_of_basis _
    (closureGenerators row80Generators 1) (closureGenerators row80Generators 0)
    (closureGenerators row80Generators 2 * closureGenerators row80Generators 3) row80Chart
  decide +kernel

theorem row82Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row82Interface.top (Fin 12)) 1 := by
  let h := closureGenerators row82Generators 0
  let c := closureGenerators row82Generators 3
  apply BinaryPairedTernaryCentralFlipPolynomial.uniform_of_basis _
    (closureGenerators row82Generators 1) (h * (c * h * c⁻¹)) (h * c) row82Chart
  decide +kernel

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedTernaryFlipWordNaturalFamily

end
