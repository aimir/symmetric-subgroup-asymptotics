import SymmetricSubgroupAsymptotics.BinaryTwistedQuartetLoewyCoordinates

/-! The literal middle chart has exactly the constant-plane kernel on
the radical. No dimension or head bound is assumed. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.BinaryTwistedQuartetMiddleKernel
open BinaryTwistedQuartetPolynomial (Bit Plane cubic)
open BinaryTwistedQuartetLoewyCoordinates

theorem reconstruct (v : Space) :
    v=constant (v 0)+
      ![0,(middle v).1+(middle v).2,
        cubic ((middle v).1)+cubic (cubic ((middle v).2)),
        (middle v).1+(middle v).2+
          cubic ((middle v).1)+cubic (cubic ((middle v).2))+sumBlocks v] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [constant,middle,cubic,sumBlocks,Matrix.vecHead,Matrix.vecTail] <;>
    (try ring_nf) <;>
    simp only [show (2 : Bit)=0 by decide,show (3 : Bit)=1 by decide,
      show (4 : Bit)=0 by decide,
      show (6 : Bit)=0 by decide,
      show (8 : Bit)=0 by decide,
      show (10 : Bit)=0 by decide,show (16 : Bit)=0 by decide,
      mul_zero,mul_one,add_zero,zero_add] <;>
    simp [add_assoc]

theorem eq_constant (v : Space) (hrad : sumBlocks v=0) (hm : middle v=0) :
    v=constant (v 0) := by
  rw [reconstruct v,hm,hrad]
  funext i j
  fin_cases i <;> fin_cases j <;> simp [constant,cubic]

end SymmetricSubgroupAsymptotics.BinaryTwistedQuartetMiddleKernel
