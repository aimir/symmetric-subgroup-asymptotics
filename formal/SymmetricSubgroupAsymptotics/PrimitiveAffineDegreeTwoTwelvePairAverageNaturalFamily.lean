import SymmetricSubgroupAsymptotics.BinaryPairTernaryAveragePolynomial
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100

/-! Three original capacity-two natural fields from one prescribed
ternary-average algebra formula. The basis checks use the retained
generator tuples and physical twelve-point coordinates directly. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelvePairAverageNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

theorem row63Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row63Interface.top (Fin 12)) 2 := by
  apply BinaryPairTernaryAveragePolynomial.uniform_of_basis 0 _
    (closureGenerators row63Generators 0) (closureGenerators row63Generators 1)
    (closureGenerators row63Generators 2)
  decide +kernel

theorem row92Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row92Interface.top (Fin 12)) 2 := by
  apply BinaryPairTernaryAveragePolynomial.uniform_of_basis 1 _
    (closureGenerators row92Generators 1) (closureGenerators row92Generators 2)
    (closureGenerators row92Generators 3)
  decide +kernel

theorem row93Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row93Interface.top (Fin 12)) 2 := by
  apply BinaryPairTernaryAveragePolynomial.uniform_of_basis 2 _
    (closureGenerators row93Generators 1) (closureGenerators row93Generators 2)
    (closureGenerators row93Generators 3)
  decide +kernel

end PrimitiveAffineDegreeTwoTwelvePairAverageNaturalFamily
end SymmetricSubgroupAsymptotics

end
