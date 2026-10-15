import SymmetricSubgroupAsymptotics.BinaryQuaternaryTriplePolynomial
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50

/-! The original row31 generators realize the two operators in the
quaternary three-block template. This establishes the retained natural
capacity two directly on the original top and its original points. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow31NaturalModule

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

abbrev Top := Row31Top

def t : Top := closureGenerators row31Generators 0
def s : Top := closureGenerators row31Generators 1

def representation := permutationFunctionRepresentation (ZMod 2) Top (Fin 12)

theorem translation_binding :
    (t : Equiv.Perm (Fin 12)) = BinaryQuaternaryTriplePolynomial.translation := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem rotation_binding :
    (s : Equiv.Perm (Fin 12)) = BinaryQuaternaryTriplePolynomial.rotation := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem translation_action : representation t =
    BinaryQuaternaryTriplePolynomial.representation
      BinaryQuaternaryTriplePolynomial.translation := by
  apply LinearMap.ext
  intro v
  funext x
  change v ((t : Equiv.Perm (Fin 12))⁻¹ x) =
    v (BinaryQuaternaryTriplePolynomial.translation⁻¹ x)
  rw [translation_binding]

theorem rotation_action : representation s =
    BinaryQuaternaryTriplePolynomial.representation
      BinaryQuaternaryTriplePolynomial.rotation := by
  apply LinearMap.ext
  intro v
  funext x
  change v ((s : Equiv.Perm (Fin 12))⁻¹ x) =
    v (BinaryQuaternaryTriplePolynomial.rotation⁻¹ x)
  rw [rotation_binding]

theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row31Interface.top (Fin 12)) 2 :=
  BinaryQuaternaryTriplePolynomial.uniform representation t s
    translation_action rotation_action

end PrimitiveAffineDegreeTwoTwelveRow31NaturalModule
end SymmetricSubgroupAsymptotics

end
