import SymmetricSubgroupAsymptotics.BinaryPairedFiveCycleCentralFlipPolynomial
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150

/-! The original paired five-cycle, global flip, and mover in row124
realize the common projected polynomial operator. The natural capacity
is exactly the stored one. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedFiveCycleCentralFlipNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

theorem row124Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row124Interface.top (Fin 12)) 1 := by
  apply BinaryPairedFiveCycleCentralFlipPolynomial.uniform_of_basis _
    (closureGenerators row124Generators 1) (closureGenerators row124Generators 0)
    (closureGenerators row124Generators 2) (Equiv.refl _)
  decide +kernel

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedFiveCycleCentralFlipNaturalFamily

end
