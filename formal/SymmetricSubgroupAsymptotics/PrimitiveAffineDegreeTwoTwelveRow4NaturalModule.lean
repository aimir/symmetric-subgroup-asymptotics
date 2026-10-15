import SymmetricSubgroupAsymptotics.BinaryKleinNormTriplePolynomial
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50

/-! The original row4 natural bound at its retained capacity three.
The normal Klein-four norm supplies a shared radical operator. Its
three polynomial generators bound every invariant subspace by the PID
theorem, with a literal basis check on the original twelve points. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow4NaturalModule

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def t : Row4Top := closureGenerators row4Generators 0
def s : Row4Top := closureGenerators row4Generators 1
def u : Row4Top := t * s * t⁻¹ * s⁻¹
def v : Row4Top := t * u * t⁻¹

theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row4Interface.top (Fin 12)) 3 := by
  apply BinaryKleinNormTriplePolynomial.uniform_of_basis _ t u v
  decide +kernel

end PrimitiveAffineDegreeTwoTwelveRow4NaturalModule
end SymmetricSubgroupAsymptotics

end
