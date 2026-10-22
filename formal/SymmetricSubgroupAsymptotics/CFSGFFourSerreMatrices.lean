import SymmetricSubgroupAsymptotics.CFSGFFourE6Generators
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Literal diagram-folded E6 matrices in the pinned F4 node order.
The E6 orbits are {0,5}, {2,4}, {3}, {1}. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices

def cartan (i : Fin 4) : Mat := ![e6H 0+e6H 5,e6H 2+e6H 4,e6H 3,e6H 1] i
def positive (i : Fin 4) : Mat := ![e6E 0+e6E 5,e6E 2+e6E 4,e6E 3,e6E 1] i
def negative (i : Fin 4) : Mat := ![e6F 0+e6F 5,e6F 2+e6F 4,e6F 3,e6F 1] i
def representative (i : Fin 4) : Fin 6 := ![0,2,3,1] i

end SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
