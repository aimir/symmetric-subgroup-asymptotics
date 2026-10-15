import SymmetricSubgroupAsymptotics.BinaryTwistedAlternatingTriplePolynomial
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301

/-! Four original natural-module bounds from the common twisted
three-block polynomial operator. The first and third literal generators
give k and r. The block mover is generator3 in rows166 and228, and the
ordered product generator3*generator4 in rows207 and254. All conclusions
retain the original literal tops and their stored capacity one. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveTwistedAlternatingNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

theorem row166Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row166Interface.top (Fin 12)) 1 := by
  apply BinaryTwistedAlternatingTriplePolynomial.uniform_subgroup 0 Row166Top
    (closureGenerators row166Generators 0) (closureGenerators row166Generators 2)
    (closureGenerators row166Generators 3)
  all_goals
    apply Equiv.ext
    intro x
    revert x
    decide +kernel

theorem row207Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row207Interface.top (Fin 12)) 1 := by
  apply BinaryTwistedAlternatingTriplePolynomial.uniform_subgroup 1 Row207Top
    (closureGenerators row207Generators 0) (closureGenerators row207Generators 2)
    (closureGenerators row207Generators 3 * closureGenerators row207Generators 4)
  all_goals
    apply Equiv.ext
    intro x
    revert x
    decide +kernel

theorem row228Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row228Interface.top (Fin 12)) 1 := by
  apply BinaryTwistedAlternatingTriplePolynomial.uniform_subgroup 2 Row228Top
    (closureGenerators row228Generators 0) (closureGenerators row228Generators 2)
    (closureGenerators row228Generators 3)
  all_goals
    apply Equiv.ext
    intro x
    revert x
    decide +kernel

theorem row254Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row254Interface.top (Fin 12)) 1 := by
  apply BinaryTwistedAlternatingTriplePolynomial.uniform_subgroup 3 Row254Top
    (closureGenerators row254Generators 0) (closureGenerators row254Generators 2)
    (closureGenerators row254Generators 3 * closureGenerators row254Generators 4)
  all_goals
    apply Equiv.ext
    intro x
    revert x
    decide +kernel

end PrimitiveAffineDegreeTwoTwelveTwistedAlternatingNaturalFamily
end SymmetricSubgroupAsymptotics

end
