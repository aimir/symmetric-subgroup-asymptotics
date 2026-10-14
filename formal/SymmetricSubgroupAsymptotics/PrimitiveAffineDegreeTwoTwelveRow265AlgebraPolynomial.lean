import SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitness
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301

/-!
# A cyclic algebra operator for the local alternating four-point action

The original row265 generators are a=(2,5,11), b=(2,5,8), and the
shift c by four. Thus a,b act on one four-point block and c cycles
three such blocks. Put E=1+a+a² and L=E*(a*b)*E+1+a². On the local
block, L interchanges the two C3-fixed coordinates and acts by a on
their complementary two-dimensional space; on other blocks L=1.

The operator c*L is cyclic on the twelve-point module. The twelve
displayed iterates of delta5 and their inverse matrix certify this
directly. Every invariant subspace is therefore cyclic by the PID
polynomial-module theorem; no invariant-state list is used.
-/

set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow265AlgebraPolynomial

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

abbrev Top := row265Interface.top

def a : Top := closureGenerators row265Generators 0
def b : Top := closureGenerators row265Generators 1
def c : Top := closureGenerators row265Generators 2

def representation := permutationFunctionRepresentation (ZMod 2) Top (Fin 12)

def averagingOperator : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  1 + representation a + representation (a ^ 2)

def localOperator : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  averagingOperator * representation (a * b) * averagingOperator + 1 +
    representation (a ^ 2)

def operator : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  representation c * localOperator

def averagingElement : (ZMod 2)[Top] :=
  1 + MonoidAlgebra.single a 1 + MonoidAlgebra.single (a ^ 2) 1

def algebraElement : (ZMod 2)[Top] :=
  MonoidAlgebra.single c 1 *
    (averagingElement * MonoidAlgebra.single (a * b) 1 * averagingElement + 1 +
      MonoidAlgebra.single (a ^ 2) 1)

theorem operator_eq : operator = representation.asAlgebraHom algebraElement := by
  simp only [operator, localOperator, averagingOperator, algebraElement,
    averagingElement, map_mul, map_add, map_one,
    Representation.asAlgebraHom_single, one_smul]

def vectorMask (m : Fin 12) : ℕ :=
  (#[32, 577, 1042, 292, 64, 1024, 4, 73, 1168, 2308, 8, 128] : Array ℕ)[m.val]!

def vectors (_ : Fin 1) (m : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (vectorMask m)

def coefficientMask (i : Fin 12) : ℕ :=
  (#[1168, 2308, 64, 1024, 2336, 1, 16, 2048, 73, 1154, 32, 521] : Array ℕ)[i.val]!

def coefficient (i : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (coefficientMask i)

private theorem step_checked : ∀ (m : Fin 11) (x : Fin 12),
    vectors 0 m.succ x = operator (vectors 0 m.castSucc) x := by
  decide +kernel

private theorem point_checked : ∀ i x : Fin 12,
    (∑ j, coefficient i j * vectors 0 j x) = (Pi.single i 1 : Fin 12 → ZMod 2) x := by
  decide +kernel

def polynomialWitness : LiteralPolynomialSpanWitness operator 1 11 where
  vectors := vectors
  step _ m := by
    funext x
    exact step_checked m x
  selected j := (0, j)
  coefficient := coefficient
  point_eq := point_checked

theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row265Interface.top (Fin 12)) 1 :=
  polynomialWitness.uniform representation algebraElement operator_eq

end PrimitiveAffineDegreeTwoTwelveRow265AlgebraPolynomial
end SymmetricSubgroupAsymptotics

end
