import SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitness
import Mathlib.Data.Matrix.Mul

/-! A genuine cubic local twist needs two binary seeds. For T=a+t,
the four Krylov vectors from a plane vector u at block zero are
(u,0,0,0), (Bu,0,0,u), (Bu,Bu,0,Bu), (u,B²u,u,Bu).
The displayed inverse uses B²+B+1=0. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryTwistedQuartetPolynomial
abbrev Bit := ZMod 2
abbrev Vector := Fin 8 → Bit
abbrev Plane := Fin 2 → Bit

def cubic (u : Plane) : Plane := ![u 1,u 0+u 1]
def block (v : Vector) (i : Fin 4) : Plane := fun j => v ⟨2*i.val+j.val,by omega⟩

def matrix : Matrix (Fin 8) (Fin 8) Bit :=
  ![![0,1,0,0,0,0,1,0],
    ![1,1,0,0,0,0,0,1],
    ![0,0,0,0,1,0,0,1],
    ![0,0,0,0,0,1,1,1],
    ![0,0,1,1,0,0,0,0],
    ![0,0,1,0,0,0,0,0],
    ![1,0,0,0,0,1,0,0],
    ![0,1,0,0,1,1,0,0]]

def operator : Module.End Bit Vector := matrix.mulVecLin

def seed (j : Fin 2) : Vector := Pi.single ⟨j.val,by omega⟩ 1

def vectors (j : Fin 2) (m : Fin 4) : Vector := (operator^m.val) (seed j)

def inverseCoefficients (v : Vector) : Fin 4 → Plane :=
  ![block v 0+cubic (cubic (block v 1))+cubic (block v 3),
    block v 1+block v 2+block v 3,
    cubic (cubic (block v 1))+cubic (block v 2),
    block v 2]

def selected (j : Fin 8) : Fin 2 × Fin 4 :=
  (⟨j.val/4,by omega⟩,⟨j.val%4,by omega⟩)

def coefficient (i j : Fin 8) : Bit :=
  inverseCoefficients (Pi.single i 1) (selected j).2 (selected j).1

def witness : LiteralPolynomialSpanWitness operator 2 3 where
  vectors := vectors
  step j m := by
    dsimp only [vectors]
    rw [show m.succ.val=m.castSucc.val+1 from rfl,pow_succ']
    rfl
  selected := selected
  coefficient := coefficient
  point_eq := by
    intro i x
    revert i x
    decide +kernel

end SymmetricSubgroupAsymptotics.BinaryTwistedQuartetPolynomial
