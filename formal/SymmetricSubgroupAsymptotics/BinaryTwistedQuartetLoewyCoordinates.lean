import SymmetricSubgroupAsymptotics.BinaryTwistedQuartetPolynomial

/-! Literal Loewy coordinates of the cubic-twisted quartet module.
These identities do not assume that an invariant binary subspace is
stable under an extra F4 scalar operator. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.BinaryTwistedQuartetLoewyCoordinates
open BinaryTwistedQuartetPolynomial (Bit Plane cubic)
abbrev Space := Fin 4 → Plane

def sumBlocks (v : Space) : Plane := v 0+v 1+v 2+v 3
def constant (u : Plane) : Space := fun _ => u

def cycleAction (v : Space) : Space :=
  ![cubic (v 0),cubic (v 3),cubic (v 1),cubic (v 2)]

def flipAction (v : Space) : Space := ![v 3,v 2,v 1,v 0]

def middle (v : Space) : Plane × Plane :=
  let p := v 1+v 0
  let q := v 2+v 0
  (cubic (cubic p)+q,q+cubic p)

def representative (p q : Plane) : Space := ![0,p,q,p+q]

theorem sum_cycle (v : Space) : sumBlocks (cycleAction v)=cubic (sumBlocks v) := by
  ext i
  fin_cases i <;> simp [sumBlocks,cycleAction,cubic] <;> ring

theorem cycle_constant (u : Plane) : cycleAction (constant u)=constant (cubic u) := by
  funext i
  fin_cases i <;> rfl

theorem middle_cycle_first (v : Space) :
    (middle (cycleAction v)).1=(middle v).1+sumBlocks v := by
  ext i
  fin_cases i <;> simp [middle,cycleAction,sumBlocks,cubic,Matrix.vecHead,Matrix.vecTail] <;> ring_nf <;>
    simp only [show (2 : Bit)=0 by decide,show (3 : Bit)=1 by decide,
      show (4 : Bit)=0 by decide,show (5 : Bit)=1 by decide,
      show (6 : Bit)=0 by decide,show (7 : Bit)=1 by decide,
      mul_zero,mul_one,add_zero,zero_add] <;> ring

theorem middle_cycle_second (v : Space) :
    (middle (cycleAction v)).2=
      cubic (cubic ((middle v).2))+cubic (cubic (sumBlocks v)) := by
  ext i
  fin_cases i <;> simp [middle,cycleAction,sumBlocks,cubic,Matrix.vecHead,Matrix.vecTail] <;> ring_nf <;>
    simp only [show (2 : Bit)=0 by decide,show (3 : Bit)=1 by decide,
      show (4 : Bit)=0 by decide,show (5 : Bit)=1 by decide,
      show (6 : Bit)=0 by decide,show (7 : Bit)=1 by decide,
      mul_zero,mul_one,add_zero,zero_add] <;> ring

theorem middle_constant (u : Plane) : middle (constant u)=0 := by
  apply Prod.ext <;> ext i <;> fin_cases i <;>
    simp [middle,constant,cubic,Matrix.vecHead,Matrix.vecTail] <;> ring_nf <;>
    simp only [show (2 : Bit)=0 by decide,show (3 : Bit)=1 by decide,
      show (4 : Bit)=0 by decide,show (5 : Bit)=1 by decide,
      show (6 : Bit)=0 by decide,show (7 : Bit)=1 by decide,
      mul_zero,mul_one,add_zero,zero_add] <;> ring

theorem representative_sum (p q : Plane) : sumBlocks (representative p q)=0 := by
  ext i
  fin_cases i <;> simp [sumBlocks,representative] <;> ring_nf <;>
    simp only [show (2 : Bit)=0 by decide,show (3 : Bit)=1 by decide,
      show (4 : Bit)=0 by decide,show (5 : Bit)=1 by decide,
      show (6 : Bit)=0 by decide,show (7 : Bit)=1 by decide,
      mul_zero,mul_one,add_zero,zero_add] <;> ring

/-- The middle layer splits into two trivial binary coordinates and
one nontrivial binary cubic coordinate. -/
theorem middle_cycle_on_radical (v : Space) (hv : sumBlocks v=0) :
    middle (cycleAction v)=((middle v).1,cubic (cubic ((middle v).2))) := by
  apply Prod.ext
  · rw [middle_cycle_first,hv,add_zero]
  · rw [middle_cycle_second,hv]
    simp [cubic]

end SymmetricSubgroupAsymptotics.BinaryTwistedQuartetLoewyCoordinates
