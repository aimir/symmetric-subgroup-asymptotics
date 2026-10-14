import SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitness
import SymmetricSubgroupAsymptotics.BinaryQuadraticField
import Mathlib.Data.Matrix.Mul

/-! The same four-coordinate cyclic operator over F2 and F4. The matrix
is E*t*E+1+a² for a=(1,2,3), t=(0,3)(1,2), E=1+a+a². -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics
namespace BinaryLocalAlternatingFourPolynomial

def matrix (K : Type) [Semiring K] : Matrix (Fin 4) (Fin 4) K :=
  ![![0, 1, 1, 1], ![1, 1, 1, 0], ![1, 0, 1, 1], ![1, 1, 0, 1]]

def operator (K : Type) [Field K] : Module.End K (Fin 4 → K) :=
  (matrix K).mulVecLin

def vectors (K : Type) [Semiring K] (_ : Fin 1) : Fin 4 → Fin 4 → K :=
  ![![0, 0, 0, 1], ![1, 0, 1, 1], ![0, 0, 1, 0], ![1, 1, 1, 0]]

def coefficient (K : Type) [Semiring K] : Fin 4 → Fin 4 → K :=
  ![![1, 1, 1, 0], ![1, 1, 0, 1], ![0, 0, 1, 0], ![1, 0, 0, 0]]

def binaryWitness : LiteralPolynomialSpanWitness (operator (ZMod 2)) 1 3 where
  vectors := vectors (ZMod 2)
  step j m := by
    funext x
    revert j m x
    decide +kernel
  selected j := (0, j)
  coefficient := coefficient (ZMod 2)
  point_eq := by decide +kernel

def quadraticWitness :
    LiteralPolynomialSpanWitness (operator BinaryQuadraticField.Scalar) 1 3 where
  vectors := vectors BinaryQuadraticField.Scalar
  step j m := by
    funext x
    revert j m x
    decide +kernel
  selected j := (0, j)
  coefficient := coefficient BinaryQuadraticField.Scalar
  point_eq := by decide +kernel

end BinaryLocalAlternatingFourPolynomial
end SymmetricSubgroupAsymptotics

end
