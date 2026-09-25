import SymmetricSubgroupAsymptotics.BinaryPermutationBlocks
import SymmetricSubgroupAsymptotics.BinaryExceptional8T16
import SymmetricSubgroupAsymptotics.BinaryExceptional8T20
import SymmetricSubgroupAsymptotics.BinaryExceptional8T21
import SymmetricSubgroupAsymptotics.BinaryExceptional16T1086

/-!
# Physical orbit words of the four exceptional carriers

Every displayed block uses actual coordinates in the original point set.
Generator intertwiners and two-way generator words prove the whole block
projection is the literal base-alphabet action. The blocks cover exactly
the original physical set, with no auxiliary quotient points counted.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics

namespace BinaryChart8T16

private def block0ImagesLiteral0 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,3,0,5,6,7,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,0,1,2,7,4,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0ImagesLiteral1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0Images (i : Fin 2) : Equiv.Perm (Fin 8) :=
  (if i.val < 1 then block0ImagesLiteral0 else block0ImagesLiteral1)

private def block0BaseElementLiteral0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral1 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,7,4,5,6,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,6,3,4,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral2 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral3 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral4 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,7,0,5,6,3,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,0,1,6,7,4,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral5 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,3,4,5,6,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,2,3,4,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral6 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,0,1,6,3,4,5,2] : Array (Fin 8))[x.val]!
  invFun x := (#[1,2,7,4,5,6,3,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral7 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,1,6,3,4,5] : Array (Fin 8))[x.val]!
  invFun x := (#[2,3,0,5,6,7,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral8 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,4,5,6,3,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,0,5,2,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral9 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,0,5,6,7,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,1,6,3,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral10 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,3,0,5,6,7,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,0,1,2,7,4,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral11 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,0,1,2,3,4,5,6] : Array (Fin 8))[x.val]!
  invFun x := (#[1,2,3,4,5,6,7,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral12 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,0,5,6,3,4,1,2] : Array (Fin 8))[x.val]!
  invFun x := (#[1,6,7,4,5,2,3,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral13 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,4,1,6,3,0,5,2] : Array (Fin 8))[x.val]!
  invFun x := (#[5,2,7,4,1,6,3,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral14 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral15 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,0,1,6,7,4,5,2] : Array (Fin 8))[x.val]!
  invFun x := (#[1,2,7,0,5,6,3,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral16 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,0,1,6,7,4,5] : Array (Fin 8))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral17 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral18 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,6,3,4,5,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,6,3,4,5,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral19 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,2,3,4,1,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,2,3,4,1,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral20 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,0,5,2,3,4,1,6] : Array (Fin 8))[x.val]!
  invFun x := (#[1,6,3,4,5,2,7,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral21 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,2,3,0,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,2,3,0,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral22 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,4,1,2,3,0,5,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,2,3,4,1,6,7,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral23 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,4,5,6,3,0,1,2] : Array (Fin 8))[x.val]!
  invFun x := (#[5,6,7,4,1,2,3,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral24 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,0,1,2,7,4,5,6] : Array (Fin 8))[x.val]!
  invFun x := (#[1,2,3,0,5,6,7,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral25 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,0,5,6,7,4,1,2] : Array (Fin 8))[x.val]!
  invFun x := (#[1,6,7,0,5,2,3,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral26 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,4,1,6,7,0,5,2] : Array (Fin 8))[x.val]!
  invFun x := (#[5,2,7,0,1,6,3,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral27 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,4,1,6,7,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,0,1,2,7,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral28 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,6,7,4,5,2,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,5,6,3,4,1,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral29 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral30 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,2,7,4,1,6,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,4,1,6,3,0,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral31 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral32 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,6,3,4,1,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,6,3,4,1,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral33 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,2,7,0,5,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,2,7,0,5,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral34 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral35 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,2,3,0,1,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,2,3,0,1,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral36 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,4,5,2,3,0,1,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,6,3,4,1,2,7,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral37 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,0,5,2,7,4,1,6] : Array (Fin 8))[x.val]!
  invFun x := (#[1,6,3,0,5,2,7,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral38 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,4,1,2,7,0,5,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,2,3,0,1,6,7,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral39 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,4,5,6,7,0,1,2] : Array (Fin 8))[x.val]!
  invFun x := (#[5,6,7,0,1,2,3,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral40 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,7,0,5,2,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,4,5,6,3,0,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral41 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,6,7,0,5,2,3,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,0,5,6,7,4,1,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral42 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,6,3,4,5,2,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,5,2,3,4,1,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral43 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,2,7,0,1,6,3,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,4,1,6,7,0,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral44 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,2,3,4,1,6,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,4,1,2,3,0,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral45 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,6,7,4,1,2,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,4,5,6,3,0,1,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral46 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,6,7,4,1,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,6,7,4,1,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral47 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,6,7,0,5,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,6,7,0,5,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral48 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,2,7,0,1,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,2,7,0,1,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral49 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,6,3,0,1,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,6,3,0,1,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral50 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,4,5,2,7,0,1,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,6,3,0,1,2,7,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral51 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  invFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral52 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,7,4,5,2,3,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral53 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral54 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,6,3,0,5,2,7,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,0,5,2,7,4,1,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral55 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,2,3,0,1,6,7,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,4,1,2,7,0,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral56 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,6,7,0,1,2,3,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,4,5,6,7,0,1,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral57 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,6,3,4,1,2,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,4,5,2,3,0,1,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral58 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral59 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,7,4,1,2,3,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,4,5,2,7,0,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral60 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,0,1,2,7,4,5] : Array (Fin 8))[x.val]!
  invFun x := (#[2,3,4,1,6,7,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral61 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,4,5,2,7,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,4,1,2,3,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral62 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,6,3,0,1,2,7,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,4,5,2,7,0,1,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral63 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,4,1,2,7,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,4,1,2,7,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElement (i : Fin 64) : Equiv.Perm (Fin 8) :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then block0BaseElementLiteral0 else block0BaseElementLiteral1) else (if i.val < 3 then block0BaseElementLiteral2 else block0BaseElementLiteral3)) else (if i.val < 6 then (if i.val < 5 then block0BaseElementLiteral4 else block0BaseElementLiteral5) else (if i.val < 7 then block0BaseElementLiteral6 else block0BaseElementLiteral7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then block0BaseElementLiteral8 else block0BaseElementLiteral9) else (if i.val < 11 then block0BaseElementLiteral10 else block0BaseElementLiteral11)) else (if i.val < 14 then (if i.val < 13 then block0BaseElementLiteral12 else block0BaseElementLiteral13) else (if i.val < 15 then block0BaseElementLiteral14 else block0BaseElementLiteral15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then block0BaseElementLiteral16 else block0BaseElementLiteral17) else (if i.val < 19 then block0BaseElementLiteral18 else block0BaseElementLiteral19)) else (if i.val < 22 then (if i.val < 21 then block0BaseElementLiteral20 else block0BaseElementLiteral21) else (if i.val < 23 then block0BaseElementLiteral22 else block0BaseElementLiteral23))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then block0BaseElementLiteral24 else block0BaseElementLiteral25) else (if i.val < 27 then block0BaseElementLiteral26 else block0BaseElementLiteral27)) else (if i.val < 30 then (if i.val < 29 then block0BaseElementLiteral28 else block0BaseElementLiteral29) else (if i.val < 31 then block0BaseElementLiteral30 else block0BaseElementLiteral31))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then block0BaseElementLiteral32 else block0BaseElementLiteral33) else (if i.val < 35 then block0BaseElementLiteral34 else block0BaseElementLiteral35)) else (if i.val < 38 then (if i.val < 37 then block0BaseElementLiteral36 else block0BaseElementLiteral37) else (if i.val < 39 then block0BaseElementLiteral38 else block0BaseElementLiteral39))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then block0BaseElementLiteral40 else block0BaseElementLiteral41) else (if i.val < 43 then block0BaseElementLiteral42 else block0BaseElementLiteral43)) else (if i.val < 46 then (if i.val < 45 then block0BaseElementLiteral44 else block0BaseElementLiteral45) else (if i.val < 47 then block0BaseElementLiteral46 else block0BaseElementLiteral47)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then block0BaseElementLiteral48 else block0BaseElementLiteral49) else (if i.val < 51 then block0BaseElementLiteral50 else block0BaseElementLiteral51)) else (if i.val < 54 then (if i.val < 53 then block0BaseElementLiteral52 else block0BaseElementLiteral53) else (if i.val < 55 then block0BaseElementLiteral54 else block0BaseElementLiteral55))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then block0BaseElementLiteral56 else block0BaseElementLiteral57) else (if i.val < 59 then block0BaseElementLiteral58 else block0BaseElementLiteral59)) else (if i.val < 62 then (if i.val < 61 then block0BaseElementLiteral60 else block0BaseElementLiteral61) else (if i.val < 63 then block0BaseElementLiteral62 else block0BaseElementLiteral63))))))

def block0BaseGenerators (j : Fin 2) := block0BaseElement (#[1,2][j.val]!)
private def block0BaseNextTable (i : Fin 64) : Array (Fin 64) :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2] else #[3,4]) else (if i.val < 3 then #[5,0] else #[6,7])) else (if i.val < 6 then (if i.val < 5 then #[8,1] else #[9,10]) else (if i.val < 7 then #[0,11] else #[12,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[13,14] else #[15,16]) else (if i.val < 11 then #[17,5] else #[18,6])) else (if i.val < 14 then (if i.val < 13 then #[19,20] else #[21,22]) else (if i.val < 15 then #[23,8] else #[2,24])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[25,9] else #[26,27]) else (if i.val < 19 then #[28,29] else #[30,31])) else (if i.val < 22 then (if i.val < 21 then #[32,12] else #[4,33]) else (if i.val < 23 then #[34,13] else #[35,36]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[29,15] else #[31,37]) else (if i.val < 27 then #[33,38] else #[39,17])) else (if i.val < 30 then (if i.val < 29 then #[40,41] else #[42,18]) else (if i.val < 31 then #[7,43] else #[44,19]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[45,46] else #[10,21]) else (if i.val < 35 then #[41,47] else #[43,48])) else (if i.val < 38 then (if i.val < 37 then #[49,23] else #[46,25]) else (if i.val < 39 then #[47,26] else #[48,50]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[11,51] else #[52,28]) else (if i.val < 43 then #[53,54] else #[14,30])) else (if i.val < 46 then (if i.val < 45 then #[16,55] else #[51,56]) else (if i.val < 47 then #[57,32] else #[54,34])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[55,35] else #[56,58]) else (if i.val < 51 then #[58,39] else #[20,40])) else (if i.val < 54 then (if i.val < 53 then #[22,59] else #[24,60]) else (if i.val < 55 then #[61,42] else #[27,44]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[59,45] else #[60,62]) else (if i.val < 59 then #[62,49] else #[36,52])) else (if i.val < 62 then (if i.val < 61 then #[37,53] else #[38,63]) else (if i.val < 63 then #[63,57] else #[50,61]))))))
private def block0BaseWordTable (i : Fin 64) : List (Fin 2) :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then [] else [0]) else (if i.val < 3 then [1] else [0,0])) else (if i.val < 6 then (if i.val < 5 then [0,1] else [1,0]) else (if i.val < 7 then [0,0,0] else [0,0,1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then [0,1,0] else [1,0,0]) else (if i.val < 11 then [1,0,1] else [0,0,0,1])) else (if i.val < 14 then (if i.val < 13 then [0,0,1,0] else [0,1,0,0]) else (if i.val < 15 then [0,1,0,1] else [1,0,0,0])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then [1,0,0,1] else [1,0,1,0]) else (if i.val < 19 then [0,0,0,1,0] else [0,0,1,0,0])) else (if i.val < 22 then (if i.val < 21 then [0,0,1,0,1] else [0,1,0,0,0]) else (if i.val < 23 then [0,1,0,0,1] else [0,1,0,1,0]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then [1,0,0,0,1] else [1,0,0,1,0]) else (if i.val < 27 then [1,0,1,0,0] else [1,0,1,0,1])) else (if i.val < 30 then (if i.val < 29 then [0,0,0,1,0,0] else [0,0,0,1,0,1]) else (if i.val < 31 then [0,0,1,0,0,0] else [0,0,1,0,0,1]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then [0,0,1,0,1,0] else [0,1,0,0,0,1]) else (if i.val < 35 then [0,1,0,0,1,0] else [0,1,0,1,0,0])) else (if i.val < 38 then (if i.val < 37 then [0,1,0,1,0,1] else [1,0,0,1,0,1]) else (if i.val < 39 then [1,0,1,0,0,1] else [1,0,1,0,1,0]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then [0,0,0,1,0,0,0] else [0,0,0,1,0,0,1]) else (if i.val < 43 then [0,0,0,1,0,1,0] else [0,0,1,0,0,0,1])) else (if i.val < 46 then (if i.val < 45 then [0,0,1,0,0,1,0] else [0,0,1,0,1,0,0]) else (if i.val < 47 then [0,0,1,0,1,0,1] else [0,1,0,0,1,0,1])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then [0,1,0,1,0,0,1] else [0,1,0,1,0,1,0]) else (if i.val < 51 then [1,0,1,0,1,0,1] else [0,0,0,1,0,0,0,1])) else (if i.val < 54 then (if i.val < 53 then [0,0,0,1,0,0,1,0] else [0,0,0,1,0,1,0,0]) else (if i.val < 55 then [0,0,0,1,0,1,0,1] else [0,0,1,0,0,1,0,1]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then [0,0,1,0,1,0,0,1] else [0,0,1,0,1,0,1,0]) else (if i.val < 59 then [0,1,0,1,0,1,0,1] else [0,0,0,1,0,0,1,0,1])) else (if i.val < 62 then (if i.val < 61 then [0,0,0,1,0,1,0,0,1] else [0,0,0,1,0,1,0,1,0]) else (if i.val < 63 then [0,0,1,0,1,0,1,0,1] else [0,0,0,1,0,1,0,1,0,1]))))))
private def block0BaseCayley : FiniteCayleyCertificate block0BaseGenerators 64 where
  elements := block0BaseElement
  identity := 0
  identity_eq := by decide +kernel
  next i j := (block0BaseNextTable i)[j.val]!
  next_eq := (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))
  words i := block0BaseWordTable i
  words_eq := (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))

def block0BaseCertificate := block0BaseCayley

def block0 : PermutationBlockChart (Y := Fin 8) betaGenerators where
  embedding := ⟨(fun x => (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!), by decide +kernel⟩
  images := block0Images
  intertwine := by decide +kernel

theorem block0_range : block0.hom.range =
    Subgroup.closure (Set.range block0BaseGenerators) := by
  rw [block0.hom_range]
  exact subgroup_closure_eq_of_generator_words block0.images block0BaseGenerators
    (fun i => (#[
  [1,0,1],
  [1]
] : Array (List (Fin 2)))[i.val]!)
    (fun j => (#[
  [1,0,1],
  [1]
] : Array (List (Fin 2)))[j.val]!)
    (by decide +kernel) (by decide +kernel)

theorem block0_base_transitive (x y : Fin 8) :
    ∃ g : Subgroup.closure (Set.range block0BaseGenerators), (g : Equiv.Perm (Fin 8)) x = y := by
  let i : Fin 64 := ((#[
  #[0,1,3,15,21,30,40,6],
  #[6,0,1,9,13,19,28,3],
  #[3,6,0,5,8,12,18,1],
  #[4,7,11,0,1,3,6,2],
  #[21,30,40,6,0,1,3,15],
  #[13,19,28,3,6,0,1,9],
  #[8,12,18,1,3,6,0,5],
  #[1,3,6,2,4,7,11,0]
] : Array (Array (Fin 64)))[x.val]!)[y.val]!
  refine ⟨⟨block0BaseCertificate.elements i,
    (block0BaseCertificate.mem_closure_iff _).mpr ⟨i,rfl⟩⟩, ?_⟩
  have h : ∀ x y : Fin 8,
      block0BaseCertificate.elements (((#[
  #[0,1,3,15,21,30,40,6],
  #[6,0,1,9,13,19,28,3],
  #[3,6,0,5,8,12,18,1],
  #[4,7,11,0,1,3,6,2],
  #[21,30,40,6,0,1,3,15],
  #[13,19,28,3,6,0,1,9],
  #[8,12,18,1,3,6,0,5],
  #[1,3,6,2,4,7,11,0]
] : Array (Array (Fin 64)))[x.val]!)[y.val]!) x = y := by decide +kernel
  exact h x y

theorem block0_base_card :
    Nat.card (Subgroup.closure (Set.range block0BaseGenerators)) = 64 :=
  block0BaseCertificate.card_closure (by decide +kernel)

theorem physical_degree : 8 = 8 := by decide +kernel

theorem blocks_cover : ∀ x : Fin 8, ∃ y, block0.embedding y = x := by decide +kernel

/-- A full literal block of positive physical size is either the
cyclic group of order four, or a degree-eight group of order above 32. -/
theorem quarter_cyclic_four_or_large_eight :
    8 ≤ 4 * 8 ∧
    ((8 = 4 ∧ IsCyclic (Subgroup.closure (Set.range block0BaseGenerators)) ∧
      Nat.card (Subgroup.closure (Set.range block0BaseGenerators)) = 4) ∨
     (8 = 8 ∧ 32 < Nat.card (Subgroup.closure (Set.range block0BaseGenerators)))) :=
  ⟨by decide +kernel, Or.inr ⟨rfl, by rw [block0_base_card]; decide +kernel⟩⟩

end BinaryChart8T16

namespace BinaryChart8T20

private def block0ImagesLiteral0 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,3,0,5,6,7,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,0,1,2,7,4,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0ImagesLiteral1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0Images (i : Fin 2) : Equiv.Perm (Fin 8) :=
  (if i.val < 1 then block0ImagesLiteral0 else block0ImagesLiteral1)

private def block0BaseElementLiteral0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral1 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,7,4,5,6,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,6,3,4,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral2 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral3 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral4 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,7,0,5,6,3,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,0,1,6,7,4,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral5 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,3,4,5,6,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,2,3,4,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral6 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,0,1,6,3,4,5,2] : Array (Fin 8))[x.val]!
  invFun x := (#[1,2,7,4,5,6,3,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral7 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,1,6,3,4,5] : Array (Fin 8))[x.val]!
  invFun x := (#[2,3,0,5,6,7,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral8 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,4,5,6,3,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,0,5,2,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral9 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,0,5,6,7,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,1,6,3,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral10 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,3,0,5,6,7,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,0,1,2,7,4,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral11 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,0,1,2,3,4,5,6] : Array (Fin 8))[x.val]!
  invFun x := (#[1,2,3,4,5,6,7,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral12 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,0,5,6,3,4,1,2] : Array (Fin 8))[x.val]!
  invFun x := (#[1,6,7,4,5,2,3,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral13 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,4,1,6,3,0,5,2] : Array (Fin 8))[x.val]!
  invFun x := (#[5,2,7,4,1,6,3,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral14 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral15 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,0,1,6,7,4,5,2] : Array (Fin 8))[x.val]!
  invFun x := (#[1,2,7,0,5,6,3,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral16 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,0,1,6,7,4,5] : Array (Fin 8))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral17 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral18 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,6,3,4,5,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,6,3,4,5,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral19 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,2,3,4,1,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,2,3,4,1,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral20 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,0,5,2,3,4,1,6] : Array (Fin 8))[x.val]!
  invFun x := (#[1,6,3,4,5,2,7,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral21 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,2,3,0,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,2,3,0,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral22 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,4,1,2,3,0,5,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,2,3,4,1,6,7,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral23 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,4,5,6,3,0,1,2] : Array (Fin 8))[x.val]!
  invFun x := (#[5,6,7,4,1,2,3,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral24 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,0,1,2,7,4,5,6] : Array (Fin 8))[x.val]!
  invFun x := (#[1,2,3,0,5,6,7,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral25 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,0,5,6,7,4,1,2] : Array (Fin 8))[x.val]!
  invFun x := (#[1,6,7,0,5,2,3,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral26 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,4,1,6,7,0,5,2] : Array (Fin 8))[x.val]!
  invFun x := (#[5,2,7,0,1,6,3,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral27 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,4,1,6,7,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,0,1,2,7,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral28 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,6,7,4,5,2,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,5,6,3,4,1,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral29 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral30 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,2,7,4,1,6,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,4,1,6,3,0,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral31 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral32 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,6,3,4,1,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,6,3,4,1,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral33 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,2,7,0,5,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,2,7,0,5,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral34 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral35 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,2,3,0,1,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,2,3,0,1,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral36 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,4,5,2,3,0,1,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,6,3,4,1,2,7,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral37 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,0,5,2,7,4,1,6] : Array (Fin 8))[x.val]!
  invFun x := (#[1,6,3,0,5,2,7,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral38 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,4,1,2,7,0,5,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,2,3,0,1,6,7,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral39 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,4,5,6,7,0,1,2] : Array (Fin 8))[x.val]!
  invFun x := (#[5,6,7,0,1,2,3,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral40 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,7,0,5,2,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,4,5,6,3,0,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral41 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,6,7,0,5,2,3,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,0,5,6,7,4,1,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral42 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,6,3,4,5,2,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,5,2,3,4,1,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral43 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,2,7,0,1,6,3,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,4,1,6,7,0,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral44 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,2,3,4,1,6,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,4,1,2,3,0,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral45 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,6,7,4,1,2,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,4,5,6,3,0,1,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral46 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,6,7,4,1,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,6,7,4,1,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral47 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,6,7,0,5,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,6,7,0,5,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral48 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,2,7,0,1,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,2,7,0,1,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral49 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,6,3,0,1,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,6,3,0,1,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral50 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,4,5,2,7,0,1,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,6,3,0,1,2,7,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral51 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  invFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral52 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,7,4,5,2,3,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral53 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral54 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,6,3,0,5,2,7,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,0,5,2,7,4,1,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral55 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,2,3,0,1,6,7,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,4,1,2,7,0,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral56 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,6,7,0,1,2,3,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,4,5,6,7,0,1,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral57 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,6,3,4,1,2,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,4,5,2,3,0,1,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral58 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral59 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,7,4,1,2,3,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,4,5,2,7,0,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral60 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,0,1,2,7,4,5] : Array (Fin 8))[x.val]!
  invFun x := (#[2,3,4,1,6,7,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral61 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,4,5,2,7,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,4,1,2,3,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral62 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,6,3,0,1,2,7,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,4,5,2,7,0,1,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral63 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,4,1,2,7,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,4,1,2,7,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElement (i : Fin 64) : Equiv.Perm (Fin 8) :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then block0BaseElementLiteral0 else block0BaseElementLiteral1) else (if i.val < 3 then block0BaseElementLiteral2 else block0BaseElementLiteral3)) else (if i.val < 6 then (if i.val < 5 then block0BaseElementLiteral4 else block0BaseElementLiteral5) else (if i.val < 7 then block0BaseElementLiteral6 else block0BaseElementLiteral7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then block0BaseElementLiteral8 else block0BaseElementLiteral9) else (if i.val < 11 then block0BaseElementLiteral10 else block0BaseElementLiteral11)) else (if i.val < 14 then (if i.val < 13 then block0BaseElementLiteral12 else block0BaseElementLiteral13) else (if i.val < 15 then block0BaseElementLiteral14 else block0BaseElementLiteral15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then block0BaseElementLiteral16 else block0BaseElementLiteral17) else (if i.val < 19 then block0BaseElementLiteral18 else block0BaseElementLiteral19)) else (if i.val < 22 then (if i.val < 21 then block0BaseElementLiteral20 else block0BaseElementLiteral21) else (if i.val < 23 then block0BaseElementLiteral22 else block0BaseElementLiteral23))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then block0BaseElementLiteral24 else block0BaseElementLiteral25) else (if i.val < 27 then block0BaseElementLiteral26 else block0BaseElementLiteral27)) else (if i.val < 30 then (if i.val < 29 then block0BaseElementLiteral28 else block0BaseElementLiteral29) else (if i.val < 31 then block0BaseElementLiteral30 else block0BaseElementLiteral31))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then block0BaseElementLiteral32 else block0BaseElementLiteral33) else (if i.val < 35 then block0BaseElementLiteral34 else block0BaseElementLiteral35)) else (if i.val < 38 then (if i.val < 37 then block0BaseElementLiteral36 else block0BaseElementLiteral37) else (if i.val < 39 then block0BaseElementLiteral38 else block0BaseElementLiteral39))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then block0BaseElementLiteral40 else block0BaseElementLiteral41) else (if i.val < 43 then block0BaseElementLiteral42 else block0BaseElementLiteral43)) else (if i.val < 46 then (if i.val < 45 then block0BaseElementLiteral44 else block0BaseElementLiteral45) else (if i.val < 47 then block0BaseElementLiteral46 else block0BaseElementLiteral47)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then block0BaseElementLiteral48 else block0BaseElementLiteral49) else (if i.val < 51 then block0BaseElementLiteral50 else block0BaseElementLiteral51)) else (if i.val < 54 then (if i.val < 53 then block0BaseElementLiteral52 else block0BaseElementLiteral53) else (if i.val < 55 then block0BaseElementLiteral54 else block0BaseElementLiteral55))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then block0BaseElementLiteral56 else block0BaseElementLiteral57) else (if i.val < 59 then block0BaseElementLiteral58 else block0BaseElementLiteral59)) else (if i.val < 62 then (if i.val < 61 then block0BaseElementLiteral60 else block0BaseElementLiteral61) else (if i.val < 63 then block0BaseElementLiteral62 else block0BaseElementLiteral63))))))

def block0BaseGenerators (j : Fin 2) := block0BaseElement (#[1,2][j.val]!)
private def block0BaseNextTable (i : Fin 64) : Array (Fin 64) :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2] else #[3,4]) else (if i.val < 3 then #[5,0] else #[6,7])) else (if i.val < 6 then (if i.val < 5 then #[8,1] else #[9,10]) else (if i.val < 7 then #[0,11] else #[12,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[13,14] else #[15,16]) else (if i.val < 11 then #[17,5] else #[18,6])) else (if i.val < 14 then (if i.val < 13 then #[19,20] else #[21,22]) else (if i.val < 15 then #[23,8] else #[2,24])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[25,9] else #[26,27]) else (if i.val < 19 then #[28,29] else #[30,31])) else (if i.val < 22 then (if i.val < 21 then #[32,12] else #[4,33]) else (if i.val < 23 then #[34,13] else #[35,36]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[29,15] else #[31,37]) else (if i.val < 27 then #[33,38] else #[39,17])) else (if i.val < 30 then (if i.val < 29 then #[40,41] else #[42,18]) else (if i.val < 31 then #[7,43] else #[44,19]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[45,46] else #[10,21]) else (if i.val < 35 then #[41,47] else #[43,48])) else (if i.val < 38 then (if i.val < 37 then #[49,23] else #[46,25]) else (if i.val < 39 then #[47,26] else #[48,50]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[11,51] else #[52,28]) else (if i.val < 43 then #[53,54] else #[14,30])) else (if i.val < 46 then (if i.val < 45 then #[16,55] else #[51,56]) else (if i.val < 47 then #[57,32] else #[54,34])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[55,35] else #[56,58]) else (if i.val < 51 then #[58,39] else #[20,40])) else (if i.val < 54 then (if i.val < 53 then #[22,59] else #[24,60]) else (if i.val < 55 then #[61,42] else #[27,44]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[59,45] else #[60,62]) else (if i.val < 59 then #[62,49] else #[36,52])) else (if i.val < 62 then (if i.val < 61 then #[37,53] else #[38,63]) else (if i.val < 63 then #[63,57] else #[50,61]))))))
private def block0BaseWordTable (i : Fin 64) : List (Fin 2) :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then [] else [0]) else (if i.val < 3 then [1] else [0,0])) else (if i.val < 6 then (if i.val < 5 then [0,1] else [1,0]) else (if i.val < 7 then [0,0,0] else [0,0,1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then [0,1,0] else [1,0,0]) else (if i.val < 11 then [1,0,1] else [0,0,0,1])) else (if i.val < 14 then (if i.val < 13 then [0,0,1,0] else [0,1,0,0]) else (if i.val < 15 then [0,1,0,1] else [1,0,0,0])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then [1,0,0,1] else [1,0,1,0]) else (if i.val < 19 then [0,0,0,1,0] else [0,0,1,0,0])) else (if i.val < 22 then (if i.val < 21 then [0,0,1,0,1] else [0,1,0,0,0]) else (if i.val < 23 then [0,1,0,0,1] else [0,1,0,1,0]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then [1,0,0,0,1] else [1,0,0,1,0]) else (if i.val < 27 then [1,0,1,0,0] else [1,0,1,0,1])) else (if i.val < 30 then (if i.val < 29 then [0,0,0,1,0,0] else [0,0,0,1,0,1]) else (if i.val < 31 then [0,0,1,0,0,0] else [0,0,1,0,0,1]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then [0,0,1,0,1,0] else [0,1,0,0,0,1]) else (if i.val < 35 then [0,1,0,0,1,0] else [0,1,0,1,0,0])) else (if i.val < 38 then (if i.val < 37 then [0,1,0,1,0,1] else [1,0,0,1,0,1]) else (if i.val < 39 then [1,0,1,0,0,1] else [1,0,1,0,1,0]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then [0,0,0,1,0,0,0] else [0,0,0,1,0,0,1]) else (if i.val < 43 then [0,0,0,1,0,1,0] else [0,0,1,0,0,0,1])) else (if i.val < 46 then (if i.val < 45 then [0,0,1,0,0,1,0] else [0,0,1,0,1,0,0]) else (if i.val < 47 then [0,0,1,0,1,0,1] else [0,1,0,0,1,0,1])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then [0,1,0,1,0,0,1] else [0,1,0,1,0,1,0]) else (if i.val < 51 then [1,0,1,0,1,0,1] else [0,0,0,1,0,0,0,1])) else (if i.val < 54 then (if i.val < 53 then [0,0,0,1,0,0,1,0] else [0,0,0,1,0,1,0,0]) else (if i.val < 55 then [0,0,0,1,0,1,0,1] else [0,0,1,0,0,1,0,1]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then [0,0,1,0,1,0,0,1] else [0,0,1,0,1,0,1,0]) else (if i.val < 59 then [0,1,0,1,0,1,0,1] else [0,0,0,1,0,0,1,0,1])) else (if i.val < 62 then (if i.val < 61 then [0,0,0,1,0,1,0,0,1] else [0,0,0,1,0,1,0,1,0]) else (if i.val < 63 then [0,0,1,0,1,0,1,0,1] else [0,0,0,1,0,1,0,1,0,1]))))))
private def block0BaseCayley : FiniteCayleyCertificate block0BaseGenerators 64 where
  elements := block0BaseElement
  identity := 0
  identity_eq := by decide +kernel
  next i j := (block0BaseNextTable i)[j.val]!
  next_eq := (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))
  words i := block0BaseWordTable i
  words_eq := (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))

def block0BaseCertificate := block0BaseCayley

def block0 : PermutationBlockChart (Y := Fin 8) betaGenerators where
  embedding := ⟨(fun x => (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!), by decide +kernel⟩
  images := block0Images
  intertwine := by decide +kernel

theorem block0_range : block0.hom.range =
    Subgroup.closure (Set.range block0BaseGenerators) := by
  rw [block0.hom_range]
  exact subgroup_closure_eq_of_generator_words block0.images block0BaseGenerators
    (fun i => (#[
  [1,0,1],
  [1]
] : Array (List (Fin 2)))[i.val]!)
    (fun j => (#[
  [1,0,1],
  [1]
] : Array (List (Fin 2)))[j.val]!)
    (by decide +kernel) (by decide +kernel)

theorem block0_base_transitive (x y : Fin 8) :
    ∃ g : Subgroup.closure (Set.range block0BaseGenerators), (g : Equiv.Perm (Fin 8)) x = y := by
  let i : Fin 64 := ((#[
  #[0,1,3,15,21,30,40,6],
  #[6,0,1,9,13,19,28,3],
  #[3,6,0,5,8,12,18,1],
  #[4,7,11,0,1,3,6,2],
  #[21,30,40,6,0,1,3,15],
  #[13,19,28,3,6,0,1,9],
  #[8,12,18,1,3,6,0,5],
  #[1,3,6,2,4,7,11,0]
] : Array (Array (Fin 64)))[x.val]!)[y.val]!
  refine ⟨⟨block0BaseCertificate.elements i,
    (block0BaseCertificate.mem_closure_iff _).mpr ⟨i,rfl⟩⟩, ?_⟩
  have h : ∀ x y : Fin 8,
      block0BaseCertificate.elements (((#[
  #[0,1,3,15,21,30,40,6],
  #[6,0,1,9,13,19,28,3],
  #[3,6,0,5,8,12,18,1],
  #[4,7,11,0,1,3,6,2],
  #[21,30,40,6,0,1,3,15],
  #[13,19,28,3,6,0,1,9],
  #[8,12,18,1,3,6,0,5],
  #[1,3,6,2,4,7,11,0]
] : Array (Array (Fin 64)))[x.val]!)[y.val]!) x = y := by decide +kernel
  exact h x y

theorem block0_base_card :
    Nat.card (Subgroup.closure (Set.range block0BaseGenerators)) = 64 :=
  block0BaseCertificate.card_closure (by decide +kernel)

theorem physical_degree : 8 = 8 := by decide +kernel

theorem blocks_cover : ∀ x : Fin 8, ∃ y, block0.embedding y = x := by decide +kernel

/-- A full literal block of positive physical size is either the
cyclic group of order four, or a degree-eight group of order above 32. -/
theorem quarter_cyclic_four_or_large_eight :
    8 ≤ 4 * 8 ∧
    ((8 = 4 ∧ IsCyclic (Subgroup.closure (Set.range block0BaseGenerators)) ∧
      Nat.card (Subgroup.closure (Set.range block0BaseGenerators)) = 4) ∨
     (8 = 8 ∧ 32 < Nat.card (Subgroup.closure (Set.range block0BaseGenerators)))) :=
  ⟨by decide +kernel, Or.inr ⟨rfl, by rw [block0_base_card]; decide +kernel⟩⟩

end BinaryChart8T20

namespace BinaryChart8T21

private def block0ImagesLiteral0 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,3,0,5,6,7,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,0,1,2,7,4,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0ImagesLiteral1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0Images (i : Fin 2) : Equiv.Perm (Fin 8) :=
  (if i.val < 1 then block0ImagesLiteral0 else block0ImagesLiteral1)

private def block0BaseElementLiteral0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral1 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,7,4,5,6,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,6,3,4,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral2 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral3 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral4 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,7,0,5,6,3,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,0,1,6,7,4,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral5 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,3,4,5,6,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,2,3,4,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral6 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,0,1,6,3,4,5,2] : Array (Fin 8))[x.val]!
  invFun x := (#[1,2,7,4,5,6,3,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral7 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,1,6,3,4,5] : Array (Fin 8))[x.val]!
  invFun x := (#[2,3,0,5,6,7,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral8 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,4,5,6,3,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,0,5,2,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral9 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,0,5,6,7,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,1,6,3,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral10 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,3,0,5,6,7,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,0,1,2,7,4,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral11 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,0,1,2,3,4,5,6] : Array (Fin 8))[x.val]!
  invFun x := (#[1,2,3,4,5,6,7,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral12 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,0,5,6,3,4,1,2] : Array (Fin 8))[x.val]!
  invFun x := (#[1,6,7,4,5,2,3,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral13 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,4,1,6,3,0,5,2] : Array (Fin 8))[x.val]!
  invFun x := (#[5,2,7,4,1,6,3,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral14 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral15 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,0,1,6,7,4,5,2] : Array (Fin 8))[x.val]!
  invFun x := (#[1,2,7,0,5,6,3,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral16 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,0,1,6,7,4,5] : Array (Fin 8))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral17 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral18 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,6,3,4,5,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,6,3,4,5,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral19 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,2,3,4,1,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,2,3,4,1,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral20 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,0,5,2,3,4,1,6] : Array (Fin 8))[x.val]!
  invFun x := (#[1,6,3,4,5,2,7,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral21 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,2,3,0,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,2,3,0,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral22 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,4,1,2,3,0,5,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,2,3,4,1,6,7,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral23 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,4,5,6,3,0,1,2] : Array (Fin 8))[x.val]!
  invFun x := (#[5,6,7,4,1,2,3,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral24 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,0,1,2,7,4,5,6] : Array (Fin 8))[x.val]!
  invFun x := (#[1,2,3,0,5,6,7,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral25 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,0,5,6,7,4,1,2] : Array (Fin 8))[x.val]!
  invFun x := (#[1,6,7,0,5,2,3,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral26 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,4,1,6,7,0,5,2] : Array (Fin 8))[x.val]!
  invFun x := (#[5,2,7,0,1,6,3,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral27 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,4,1,6,7,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,0,1,2,7,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral28 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,6,7,4,5,2,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,5,6,3,4,1,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral29 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral30 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,2,7,4,1,6,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,4,1,6,3,0,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral31 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral32 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,6,3,4,1,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,6,3,4,1,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral33 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,2,7,0,5,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,2,7,0,5,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral34 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral35 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,2,3,0,1,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,2,3,0,1,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral36 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,4,5,2,3,0,1,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,6,3,4,1,2,7,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral37 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,0,5,2,7,4,1,6] : Array (Fin 8))[x.val]!
  invFun x := (#[1,6,3,0,5,2,7,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral38 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,4,1,2,7,0,5,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,2,3,0,1,6,7,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral39 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,4,5,6,7,0,1,2] : Array (Fin 8))[x.val]!
  invFun x := (#[5,6,7,0,1,2,3,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral40 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,7,0,5,2,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,4,5,6,3,0,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral41 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,6,7,0,5,2,3,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,0,5,6,7,4,1,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral42 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,6,3,4,5,2,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,5,2,3,4,1,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral43 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,2,7,0,1,6,3,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,4,1,6,7,0,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral44 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,2,3,4,1,6,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,4,1,2,3,0,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral45 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,6,7,4,1,2,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,4,5,6,3,0,1,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral46 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,6,7,4,1,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,6,7,4,1,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral47 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,6,7,0,5,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,6,7,0,5,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral48 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,2,7,0,1,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,2,7,0,1,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral49 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,6,3,0,1,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,6,3,0,1,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral50 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,4,5,2,7,0,1,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,6,3,0,1,2,7,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral51 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  invFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral52 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,7,4,5,2,3,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral53 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral54 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,6,3,0,5,2,7,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,0,5,2,7,4,1,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral55 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,2,3,0,1,6,7,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,4,1,2,7,0,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral56 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,6,7,0,1,2,3,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,4,5,6,7,0,1,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral57 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,6,3,4,1,2,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,4,5,2,3,0,1,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral58 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral59 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,7,4,1,2,3,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,4,5,2,7,0,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral60 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,0,1,2,7,4,5] : Array (Fin 8))[x.val]!
  invFun x := (#[2,3,4,1,6,7,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral61 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,4,5,2,7,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,4,1,2,3,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral62 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,6,3,0,1,2,7,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,4,5,2,7,0,1,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral63 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,4,1,2,7,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,4,1,2,7,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElement (i : Fin 64) : Equiv.Perm (Fin 8) :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then block0BaseElementLiteral0 else block0BaseElementLiteral1) else (if i.val < 3 then block0BaseElementLiteral2 else block0BaseElementLiteral3)) else (if i.val < 6 then (if i.val < 5 then block0BaseElementLiteral4 else block0BaseElementLiteral5) else (if i.val < 7 then block0BaseElementLiteral6 else block0BaseElementLiteral7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then block0BaseElementLiteral8 else block0BaseElementLiteral9) else (if i.val < 11 then block0BaseElementLiteral10 else block0BaseElementLiteral11)) else (if i.val < 14 then (if i.val < 13 then block0BaseElementLiteral12 else block0BaseElementLiteral13) else (if i.val < 15 then block0BaseElementLiteral14 else block0BaseElementLiteral15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then block0BaseElementLiteral16 else block0BaseElementLiteral17) else (if i.val < 19 then block0BaseElementLiteral18 else block0BaseElementLiteral19)) else (if i.val < 22 then (if i.val < 21 then block0BaseElementLiteral20 else block0BaseElementLiteral21) else (if i.val < 23 then block0BaseElementLiteral22 else block0BaseElementLiteral23))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then block0BaseElementLiteral24 else block0BaseElementLiteral25) else (if i.val < 27 then block0BaseElementLiteral26 else block0BaseElementLiteral27)) else (if i.val < 30 then (if i.val < 29 then block0BaseElementLiteral28 else block0BaseElementLiteral29) else (if i.val < 31 then block0BaseElementLiteral30 else block0BaseElementLiteral31))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then block0BaseElementLiteral32 else block0BaseElementLiteral33) else (if i.val < 35 then block0BaseElementLiteral34 else block0BaseElementLiteral35)) else (if i.val < 38 then (if i.val < 37 then block0BaseElementLiteral36 else block0BaseElementLiteral37) else (if i.val < 39 then block0BaseElementLiteral38 else block0BaseElementLiteral39))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then block0BaseElementLiteral40 else block0BaseElementLiteral41) else (if i.val < 43 then block0BaseElementLiteral42 else block0BaseElementLiteral43)) else (if i.val < 46 then (if i.val < 45 then block0BaseElementLiteral44 else block0BaseElementLiteral45) else (if i.val < 47 then block0BaseElementLiteral46 else block0BaseElementLiteral47)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then block0BaseElementLiteral48 else block0BaseElementLiteral49) else (if i.val < 51 then block0BaseElementLiteral50 else block0BaseElementLiteral51)) else (if i.val < 54 then (if i.val < 53 then block0BaseElementLiteral52 else block0BaseElementLiteral53) else (if i.val < 55 then block0BaseElementLiteral54 else block0BaseElementLiteral55))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then block0BaseElementLiteral56 else block0BaseElementLiteral57) else (if i.val < 59 then block0BaseElementLiteral58 else block0BaseElementLiteral59)) else (if i.val < 62 then (if i.val < 61 then block0BaseElementLiteral60 else block0BaseElementLiteral61) else (if i.val < 63 then block0BaseElementLiteral62 else block0BaseElementLiteral63))))))

def block0BaseGenerators (j : Fin 2) := block0BaseElement (#[1,2][j.val]!)
private def block0BaseNextTable (i : Fin 64) : Array (Fin 64) :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2] else #[3,4]) else (if i.val < 3 then #[5,0] else #[6,7])) else (if i.val < 6 then (if i.val < 5 then #[8,1] else #[9,10]) else (if i.val < 7 then #[0,11] else #[12,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[13,14] else #[15,16]) else (if i.val < 11 then #[17,5] else #[18,6])) else (if i.val < 14 then (if i.val < 13 then #[19,20] else #[21,22]) else (if i.val < 15 then #[23,8] else #[2,24])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[25,9] else #[26,27]) else (if i.val < 19 then #[28,29] else #[30,31])) else (if i.val < 22 then (if i.val < 21 then #[32,12] else #[4,33]) else (if i.val < 23 then #[34,13] else #[35,36]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[29,15] else #[31,37]) else (if i.val < 27 then #[33,38] else #[39,17])) else (if i.val < 30 then (if i.val < 29 then #[40,41] else #[42,18]) else (if i.val < 31 then #[7,43] else #[44,19]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[45,46] else #[10,21]) else (if i.val < 35 then #[41,47] else #[43,48])) else (if i.val < 38 then (if i.val < 37 then #[49,23] else #[46,25]) else (if i.val < 39 then #[47,26] else #[48,50]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[11,51] else #[52,28]) else (if i.val < 43 then #[53,54] else #[14,30])) else (if i.val < 46 then (if i.val < 45 then #[16,55] else #[51,56]) else (if i.val < 47 then #[57,32] else #[54,34])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[55,35] else #[56,58]) else (if i.val < 51 then #[58,39] else #[20,40])) else (if i.val < 54 then (if i.val < 53 then #[22,59] else #[24,60]) else (if i.val < 55 then #[61,42] else #[27,44]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[59,45] else #[60,62]) else (if i.val < 59 then #[62,49] else #[36,52])) else (if i.val < 62 then (if i.val < 61 then #[37,53] else #[38,63]) else (if i.val < 63 then #[63,57] else #[50,61]))))))
private def block0BaseWordTable (i : Fin 64) : List (Fin 2) :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then [] else [0]) else (if i.val < 3 then [1] else [0,0])) else (if i.val < 6 then (if i.val < 5 then [0,1] else [1,0]) else (if i.val < 7 then [0,0,0] else [0,0,1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then [0,1,0] else [1,0,0]) else (if i.val < 11 then [1,0,1] else [0,0,0,1])) else (if i.val < 14 then (if i.val < 13 then [0,0,1,0] else [0,1,0,0]) else (if i.val < 15 then [0,1,0,1] else [1,0,0,0])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then [1,0,0,1] else [1,0,1,0]) else (if i.val < 19 then [0,0,0,1,0] else [0,0,1,0,0])) else (if i.val < 22 then (if i.val < 21 then [0,0,1,0,1] else [0,1,0,0,0]) else (if i.val < 23 then [0,1,0,0,1] else [0,1,0,1,0]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then [1,0,0,0,1] else [1,0,0,1,0]) else (if i.val < 27 then [1,0,1,0,0] else [1,0,1,0,1])) else (if i.val < 30 then (if i.val < 29 then [0,0,0,1,0,0] else [0,0,0,1,0,1]) else (if i.val < 31 then [0,0,1,0,0,0] else [0,0,1,0,0,1]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then [0,0,1,0,1,0] else [0,1,0,0,0,1]) else (if i.val < 35 then [0,1,0,0,1,0] else [0,1,0,1,0,0])) else (if i.val < 38 then (if i.val < 37 then [0,1,0,1,0,1] else [1,0,0,1,0,1]) else (if i.val < 39 then [1,0,1,0,0,1] else [1,0,1,0,1,0]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then [0,0,0,1,0,0,0] else [0,0,0,1,0,0,1]) else (if i.val < 43 then [0,0,0,1,0,1,0] else [0,0,1,0,0,0,1])) else (if i.val < 46 then (if i.val < 45 then [0,0,1,0,0,1,0] else [0,0,1,0,1,0,0]) else (if i.val < 47 then [0,0,1,0,1,0,1] else [0,1,0,0,1,0,1])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then [0,1,0,1,0,0,1] else [0,1,0,1,0,1,0]) else (if i.val < 51 then [1,0,1,0,1,0,1] else [0,0,0,1,0,0,0,1])) else (if i.val < 54 then (if i.val < 53 then [0,0,0,1,0,0,1,0] else [0,0,0,1,0,1,0,0]) else (if i.val < 55 then [0,0,0,1,0,1,0,1] else [0,0,1,0,0,1,0,1]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then [0,0,1,0,1,0,0,1] else [0,0,1,0,1,0,1,0]) else (if i.val < 59 then [0,1,0,1,0,1,0,1] else [0,0,0,1,0,0,1,0,1])) else (if i.val < 62 then (if i.val < 61 then [0,0,0,1,0,1,0,0,1] else [0,0,0,1,0,1,0,1,0]) else (if i.val < 63 then [0,0,1,0,1,0,1,0,1] else [0,0,0,1,0,1,0,1,0,1]))))))
private def block0BaseCayley : FiniteCayleyCertificate block0BaseGenerators 64 where
  elements := block0BaseElement
  identity := 0
  identity_eq := by decide +kernel
  next i j := (block0BaseNextTable i)[j.val]!
  next_eq := (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))
  words i := block0BaseWordTable i
  words_eq := (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))

def block0BaseCertificate := block0BaseCayley

def block0 : PermutationBlockChart (Y := Fin 8) betaGenerators where
  embedding := ⟨(fun x => (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!), by decide +kernel⟩
  images := block0Images
  intertwine := by decide +kernel

theorem block0_range : block0.hom.range =
    Subgroup.closure (Set.range block0BaseGenerators) := by
  rw [block0.hom_range]
  exact subgroup_closure_eq_of_generator_words block0.images block0BaseGenerators
    (fun i => (#[
  [1,0,1],
  [1]
] : Array (List (Fin 2)))[i.val]!)
    (fun j => (#[
  [1,0,1],
  [1]
] : Array (List (Fin 2)))[j.val]!)
    (by decide +kernel) (by decide +kernel)

theorem block0_base_transitive (x y : Fin 8) :
    ∃ g : Subgroup.closure (Set.range block0BaseGenerators), (g : Equiv.Perm (Fin 8)) x = y := by
  let i : Fin 64 := ((#[
  #[0,1,3,15,21,30,40,6],
  #[6,0,1,9,13,19,28,3],
  #[3,6,0,5,8,12,18,1],
  #[4,7,11,0,1,3,6,2],
  #[21,30,40,6,0,1,3,15],
  #[13,19,28,3,6,0,1,9],
  #[8,12,18,1,3,6,0,5],
  #[1,3,6,2,4,7,11,0]
] : Array (Array (Fin 64)))[x.val]!)[y.val]!
  refine ⟨⟨block0BaseCertificate.elements i,
    (block0BaseCertificate.mem_closure_iff _).mpr ⟨i,rfl⟩⟩, ?_⟩
  have h : ∀ x y : Fin 8,
      block0BaseCertificate.elements (((#[
  #[0,1,3,15,21,30,40,6],
  #[6,0,1,9,13,19,28,3],
  #[3,6,0,5,8,12,18,1],
  #[4,7,11,0,1,3,6,2],
  #[21,30,40,6,0,1,3,15],
  #[13,19,28,3,6,0,1,9],
  #[8,12,18,1,3,6,0,5],
  #[1,3,6,2,4,7,11,0]
] : Array (Array (Fin 64)))[x.val]!)[y.val]!) x = y := by decide +kernel
  exact h x y

theorem block0_base_card :
    Nat.card (Subgroup.closure (Set.range block0BaseGenerators)) = 64 :=
  block0BaseCertificate.card_closure (by decide +kernel)

theorem physical_degree : 8 = 8 := by decide +kernel

theorem blocks_cover : ∀ x : Fin 8, ∃ y, block0.embedding y = x := by decide +kernel

/-- A full literal block of positive physical size is either the
cyclic group of order four, or a degree-eight group of order above 32. -/
theorem quarter_cyclic_four_or_large_eight :
    8 ≤ 4 * 8 ∧
    ((8 = 4 ∧ IsCyclic (Subgroup.closure (Set.range block0BaseGenerators)) ∧
      Nat.card (Subgroup.closure (Set.range block0BaseGenerators)) = 4) ∨
     (8 = 8 ∧ 32 < Nat.card (Subgroup.closure (Set.range block0BaseGenerators)))) :=
  ⟨by decide +kernel, Or.inr ⟨rfl, by rw [block0_base_card]; decide +kernel⟩⟩

end BinaryChart8T21

namespace BinaryChart16T1086

private def block0ImagesLiteral0 : Equiv.Perm (Fin 4) where
  toFun x := (#[1,2,3,0] : Array (Fin 4))[x.val]!
  invFun x := (#[3,0,1,2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0ImagesLiteral1 : Equiv.Perm (Fin 4) where
  toFun x := (#[2,3,0,1] : Array (Fin 4))[x.val]!
  invFun x := (#[2,3,0,1] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0Images (i : Fin 4) : Equiv.Perm (Fin 4) :=
  (if i.val < 2 then (if i.val < 1 then block0ImagesLiteral0 else block0ImagesLiteral1) else (if i.val < 3 then block0ImagesLiteral1 else block0ImagesLiteral1))

private def block0BaseElementLiteral0 : Equiv.Perm (Fin 4) where
  toFun x := (#[0,1,2,3] : Array (Fin 4))[x.val]!
  invFun x := (#[0,1,2,3] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral1 : Equiv.Perm (Fin 4) where
  toFun x := (#[1,2,3,0] : Array (Fin 4))[x.val]!
  invFun x := (#[3,0,1,2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral2 : Equiv.Perm (Fin 4) where
  toFun x := (#[2,3,0,1] : Array (Fin 4))[x.val]!
  invFun x := (#[2,3,0,1] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElementLiteral3 : Equiv.Perm (Fin 4) where
  toFun x := (#[3,0,1,2] : Array (Fin 4))[x.val]!
  invFun x := (#[1,2,3,0] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block0BaseElement (i : Fin 4) : Equiv.Perm (Fin 4) :=
  (if i.val < 2 then (if i.val < 1 then block0BaseElementLiteral0 else block0BaseElementLiteral1) else (if i.val < 3 then block0BaseElementLiteral2 else block0BaseElementLiteral3))

def block0BaseGenerators (j : Fin 1) := block0BaseElement (#[1][j.val]!)
private def block0BaseNextTable (i : Fin 4) : Array (Fin 4) :=
  (if i.val < 2 then (if i.val < 1 then #[1] else #[2]) else (if i.val < 3 then #[3] else #[0]))
private def block0BaseWordTable (i : Fin 4) : List (Fin 1) :=
  (if i.val < 2 then (if i.val < 1 then [] else [0]) else (if i.val < 3 then [0,0] else [0,0,0]))
private def block0BaseCayley : FiniteCayleyCertificate block0BaseGenerators 4 where
  elements := block0BaseElement
  identity := 0
  identity_eq := by decide +kernel
  next i j := (block0BaseNextTable i)[j.val]!
  next_eq := (by decide +kernel)
  words i := block0BaseWordTable i
  words_eq := (by decide +kernel)

def block0BaseCertificate := block0BaseCayley

def block0 : PermutationBlockChart (Y := Fin 4) betaGenerators where
  embedding := ⟨(fun x => (#[0,3,2,1] : Array (Fin 16))[x.val]!), by decide +kernel⟩
  images := block0Images
  intertwine := by decide +kernel

theorem block0_range : block0.hom.range =
    Subgroup.closure (Set.range block0BaseGenerators) := by
  rw [block0.hom_range]
  exact subgroup_closure_eq_of_generator_words block0.images block0BaseGenerators
    (fun i => (#[
  [0],
  [0,0],
  [0,0],
  [0,0]
] : Array (List (Fin 1)))[i.val]!)
    (fun j => (#[
  [0]
] : Array (List (Fin 4)))[j.val]!)
    (by decide +kernel) (by decide +kernel)

theorem block0_base_transitive (x y : Fin 4) :
    ∃ g : Subgroup.closure (Set.range block0BaseGenerators), (g : Equiv.Perm (Fin 4)) x = y := by
  let i : Fin 4 := ((#[
  #[0,1,2,3],
  #[3,0,1,2],
  #[2,3,0,1],
  #[1,2,3,0]
] : Array (Array (Fin 4)))[x.val]!)[y.val]!
  refine ⟨⟨block0BaseCertificate.elements i,
    (block0BaseCertificate.mem_closure_iff _).mpr ⟨i,rfl⟩⟩, ?_⟩
  have h : ∀ x y : Fin 4,
      block0BaseCertificate.elements (((#[
  #[0,1,2,3],
  #[3,0,1,2],
  #[2,3,0,1],
  #[1,2,3,0]
] : Array (Array (Fin 4)))[x.val]!)[y.val]!) x = y := by decide +kernel
  exact h x y

theorem block0_base_card :
    Nat.card (Subgroup.closure (Set.range block0BaseGenerators)) = 4 :=
  block0BaseCertificate.card_closure (by decide +kernel)

private def block1ImagesLiteral0 : Equiv.Perm (Fin 4) where
  toFun x := (#[3,0,1,2] : Array (Fin 4))[x.val]!
  invFun x := (#[1,2,3,0] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block1ImagesLiteral1 : Equiv.Perm (Fin 4) where
  toFun x := (#[0,1,2,3] : Array (Fin 4))[x.val]!
  invFun x := (#[0,1,2,3] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block1ImagesLiteral2 : Equiv.Perm (Fin 4) where
  toFun x := (#[1,0,3,2] : Array (Fin 4))[x.val]!
  invFun x := (#[1,0,3,2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block1Images (i : Fin 4) : Equiv.Perm (Fin 4) :=
  (if i.val < 2 then (if i.val < 1 then block1ImagesLiteral0 else block1ImagesLiteral1) else (if i.val < 3 then block1ImagesLiteral1 else block1ImagesLiteral2))

private def block1BaseElementLiteral0 : Equiv.Perm (Fin 4) where
  toFun x := (#[0,1,2,3] : Array (Fin 4))[x.val]!
  invFun x := (#[0,1,2,3] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block1BaseElementLiteral1 : Equiv.Perm (Fin 4) where
  toFun x := (#[1,2,3,0] : Array (Fin 4))[x.val]!
  invFun x := (#[3,0,1,2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block1BaseElementLiteral2 : Equiv.Perm (Fin 4) where
  toFun x := (#[2,1,0,3] : Array (Fin 4))[x.val]!
  invFun x := (#[2,1,0,3] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block1BaseElementLiteral3 : Equiv.Perm (Fin 4) where
  toFun x := (#[2,3,0,1] : Array (Fin 4))[x.val]!
  invFun x := (#[2,3,0,1] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block1BaseElementLiteral4 : Equiv.Perm (Fin 4) where
  toFun x := (#[3,2,1,0] : Array (Fin 4))[x.val]!
  invFun x := (#[3,2,1,0] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block1BaseElementLiteral5 : Equiv.Perm (Fin 4) where
  toFun x := (#[1,0,3,2] : Array (Fin 4))[x.val]!
  invFun x := (#[1,0,3,2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block1BaseElementLiteral6 : Equiv.Perm (Fin 4) where
  toFun x := (#[3,0,1,2] : Array (Fin 4))[x.val]!
  invFun x := (#[1,2,3,0] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block1BaseElementLiteral7 : Equiv.Perm (Fin 4) where
  toFun x := (#[0,3,2,1] : Array (Fin 4))[x.val]!
  invFun x := (#[0,3,2,1] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block1BaseElement (i : Fin 8) : Equiv.Perm (Fin 4) :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then block1BaseElementLiteral0 else block1BaseElementLiteral1) else (if i.val < 3 then block1BaseElementLiteral2 else block1BaseElementLiteral3)) else (if i.val < 6 then (if i.val < 5 then block1BaseElementLiteral4 else block1BaseElementLiteral5) else (if i.val < 7 then block1BaseElementLiteral6 else block1BaseElementLiteral7)))

def block1BaseGenerators (j : Fin 2) := block1BaseElement (#[1,2][j.val]!)
private def block1BaseNextTable (i : Fin 8) : Array (Fin 8) :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2] else #[3,4]) else (if i.val < 3 then #[5,0] else #[6,7])) else (if i.val < 6 then (if i.val < 5 then #[2,1] else #[7,6]) else (if i.val < 7 then #[0,5] else #[4,3])))
private def block1BaseWordTable (i : Fin 8) : List (Fin 2) :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then [] else [0]) else (if i.val < 3 then [1] else [0,0])) else (if i.val < 6 then (if i.val < 5 then [0,1] else [1,0]) else (if i.val < 7 then [0,0,0] else [0,0,1])))
private def block1BaseCayley : FiniteCayleyCertificate block1BaseGenerators 8 where
  elements := block1BaseElement
  identity := 0
  identity_eq := by decide +kernel
  next i j := (block1BaseNextTable i)[j.val]!
  next_eq := (by decide +kernel)
  words i := block1BaseWordTable i
  words_eq := (by decide +kernel)

def block1BaseCertificate := block1BaseCayley

def block1 : PermutationBlockChart (Y := Fin 4) betaGenerators where
  embedding := ⟨(fun x => (#[4,6,7,5] : Array (Fin 16))[x.val]!), by decide +kernel⟩
  images := block1Images
  intertwine := by decide +kernel

theorem block1_range : block1.hom.range =
    Subgroup.closure (Set.range block1BaseGenerators) := by
  rw [block1.hom_range]
  exact subgroup_closure_eq_of_generator_words block1.images block1BaseGenerators
    (fun i => (#[
  [0,0,0],
  [],
  [],
  [1,0]
] : Array (List (Fin 2)))[i.val]!)
    (fun j => (#[
  [0,0,0],
  [3,0]
] : Array (List (Fin 4)))[j.val]!)
    (by decide +kernel) (by decide +kernel)

theorem block1_base_transitive (x y : Fin 4) :
    ∃ g : Subgroup.closure (Set.range block1BaseGenerators), (g : Equiv.Perm (Fin 4)) x = y := by
  let i : Fin 8 := ((#[
  #[0,1,2,4],
  #[5,0,1,3],
  #[2,4,0,1],
  #[1,3,5,0]
] : Array (Array (Fin 8)))[x.val]!)[y.val]!
  refine ⟨⟨block1BaseCertificate.elements i,
    (block1BaseCertificate.mem_closure_iff _).mpr ⟨i,rfl⟩⟩, ?_⟩
  have h : ∀ x y : Fin 4,
      block1BaseCertificate.elements (((#[
  #[0,1,2,4],
  #[5,0,1,3],
  #[2,4,0,1],
  #[1,3,5,0]
] : Array (Array (Fin 8)))[x.val]!)[y.val]!) x = y := by decide +kernel
  exact h x y

theorem block1_base_card :
    Nat.card (Subgroup.closure (Set.range block1BaseGenerators)) = 8 :=
  block1BaseCertificate.card_closure (by decide +kernel)

private def block2ImagesLiteral0 : Equiv.Perm (Fin 4) where
  toFun x := (#[2,1,0,3] : Array (Fin 4))[x.val]!
  invFun x := (#[2,1,0,3] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block2ImagesLiteral1 : Equiv.Perm (Fin 4) where
  toFun x := (#[3,2,1,0] : Array (Fin 4))[x.val]!
  invFun x := (#[3,2,1,0] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block2ImagesLiteral2 : Equiv.Perm (Fin 4) where
  toFun x := (#[1,0,3,2] : Array (Fin 4))[x.val]!
  invFun x := (#[1,0,3,2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block2ImagesLiteral3 : Equiv.Perm (Fin 4) where
  toFun x := (#[2,3,0,1] : Array (Fin 4))[x.val]!
  invFun x := (#[2,3,0,1] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block2Images (i : Fin 4) : Equiv.Perm (Fin 4) :=
  (if i.val < 2 then (if i.val < 1 then block2ImagesLiteral0 else block2ImagesLiteral1) else (if i.val < 3 then block2ImagesLiteral2 else block2ImagesLiteral3))

private def block2BaseElementLiteral0 : Equiv.Perm (Fin 4) where
  toFun x := (#[0,1,2,3] : Array (Fin 4))[x.val]!
  invFun x := (#[0,1,2,3] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block2BaseElementLiteral1 : Equiv.Perm (Fin 4) where
  toFun x := (#[1,2,3,0] : Array (Fin 4))[x.val]!
  invFun x := (#[3,0,1,2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block2BaseElementLiteral2 : Equiv.Perm (Fin 4) where
  toFun x := (#[2,1,0,3] : Array (Fin 4))[x.val]!
  invFun x := (#[2,1,0,3] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block2BaseElementLiteral3 : Equiv.Perm (Fin 4) where
  toFun x := (#[2,3,0,1] : Array (Fin 4))[x.val]!
  invFun x := (#[2,3,0,1] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block2BaseElementLiteral4 : Equiv.Perm (Fin 4) where
  toFun x := (#[3,2,1,0] : Array (Fin 4))[x.val]!
  invFun x := (#[3,2,1,0] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block2BaseElementLiteral5 : Equiv.Perm (Fin 4) where
  toFun x := (#[1,0,3,2] : Array (Fin 4))[x.val]!
  invFun x := (#[1,0,3,2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block2BaseElementLiteral6 : Equiv.Perm (Fin 4) where
  toFun x := (#[3,0,1,2] : Array (Fin 4))[x.val]!
  invFun x := (#[1,2,3,0] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block2BaseElementLiteral7 : Equiv.Perm (Fin 4) where
  toFun x := (#[0,3,2,1] : Array (Fin 4))[x.val]!
  invFun x := (#[0,3,2,1] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block2BaseElement (i : Fin 8) : Equiv.Perm (Fin 4) :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then block2BaseElementLiteral0 else block2BaseElementLiteral1) else (if i.val < 3 then block2BaseElementLiteral2 else block2BaseElementLiteral3)) else (if i.val < 6 then (if i.val < 5 then block2BaseElementLiteral4 else block2BaseElementLiteral5) else (if i.val < 7 then block2BaseElementLiteral6 else block2BaseElementLiteral7)))

def block2BaseGenerators (j : Fin 2) := block2BaseElement (#[1,2][j.val]!)
private def block2BaseNextTable (i : Fin 8) : Array (Fin 8) :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2] else #[3,4]) else (if i.val < 3 then #[5,0] else #[6,7])) else (if i.val < 6 then (if i.val < 5 then #[2,1] else #[7,6]) else (if i.val < 7 then #[0,5] else #[4,3])))
private def block2BaseWordTable (i : Fin 8) : List (Fin 2) :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then [] else [0]) else (if i.val < 3 then [1] else [0,0])) else (if i.val < 6 then (if i.val < 5 then [0,1] else [1,0]) else (if i.val < 7 then [0,0,0] else [0,0,1])))
private def block2BaseCayley : FiniteCayleyCertificate block2BaseGenerators 8 where
  elements := block2BaseElement
  identity := 0
  identity_eq := by decide +kernel
  next i j := (block2BaseNextTable i)[j.val]!
  next_eq := (by decide +kernel)
  words i := block2BaseWordTable i
  words_eq := (by decide +kernel)

def block2BaseCertificate := block2BaseCayley

def block2 : PermutationBlockChart (Y := Fin 4) betaGenerators where
  embedding := ⟨(fun x => (#[8,10,11,9] : Array (Fin 16))[x.val]!), by decide +kernel⟩
  images := block2Images
  intertwine := by decide +kernel

theorem block2_range : block2.hom.range =
    Subgroup.closure (Set.range block2BaseGenerators) := by
  rw [block2.hom_range]
  exact subgroup_closure_eq_of_generator_words block2.images block2BaseGenerators
    (fun i => (#[
  [1],
  [0,1],
  [1,0],
  [0,0]
] : Array (List (Fin 2)))[i.val]!)
    (fun j => (#[
  [0,2],
  [0]
] : Array (List (Fin 4)))[j.val]!)
    (by decide +kernel) (by decide +kernel)

theorem block2_base_transitive (x y : Fin 4) :
    ∃ g : Subgroup.closure (Set.range block2BaseGenerators), (g : Equiv.Perm (Fin 4)) x = y := by
  let i : Fin 8 := ((#[
  #[0,1,2,4],
  #[5,0,1,3],
  #[2,4,0,1],
  #[1,3,5,0]
] : Array (Array (Fin 8)))[x.val]!)[y.val]!
  refine ⟨⟨block2BaseCertificate.elements i,
    (block2BaseCertificate.mem_closure_iff _).mpr ⟨i,rfl⟩⟩, ?_⟩
  have h : ∀ x y : Fin 4,
      block2BaseCertificate.elements (((#[
  #[0,1,2,4],
  #[5,0,1,3],
  #[2,4,0,1],
  #[1,3,5,0]
] : Array (Array (Fin 8)))[x.val]!)[y.val]!) x = y := by decide +kernel
  exact h x y

theorem block2_base_card :
    Nat.card (Subgroup.closure (Set.range block2BaseGenerators)) = 8 :=
  block2BaseCertificate.card_closure (by decide +kernel)

private def block3ImagesLiteral0 : Equiv.Perm (Fin 4) where
  toFun x := (#[1,2,3,0] : Array (Fin 4))[x.val]!
  invFun x := (#[3,0,1,2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block3ImagesLiteral1 : Equiv.Perm (Fin 4) where
  toFun x := (#[0,1,2,3] : Array (Fin 4))[x.val]!
  invFun x := (#[0,1,2,3] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block3ImagesLiteral2 : Equiv.Perm (Fin 4) where
  toFun x := (#[1,0,3,2] : Array (Fin 4))[x.val]!
  invFun x := (#[1,0,3,2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block3ImagesLiteral3 : Equiv.Perm (Fin 4) where
  toFun x := (#[2,3,0,1] : Array (Fin 4))[x.val]!
  invFun x := (#[2,3,0,1] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block3Images (i : Fin 4) : Equiv.Perm (Fin 4) :=
  (if i.val < 2 then (if i.val < 1 then block3ImagesLiteral0 else block3ImagesLiteral1) else (if i.val < 3 then block3ImagesLiteral2 else block3ImagesLiteral3))

private def block3BaseElementLiteral0 : Equiv.Perm (Fin 4) where
  toFun x := (#[0,1,2,3] : Array (Fin 4))[x.val]!
  invFun x := (#[0,1,2,3] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block3BaseElementLiteral1 : Equiv.Perm (Fin 4) where
  toFun x := (#[1,2,3,0] : Array (Fin 4))[x.val]!
  invFun x := (#[3,0,1,2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block3BaseElementLiteral2 : Equiv.Perm (Fin 4) where
  toFun x := (#[2,1,0,3] : Array (Fin 4))[x.val]!
  invFun x := (#[2,1,0,3] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block3BaseElementLiteral3 : Equiv.Perm (Fin 4) where
  toFun x := (#[2,3,0,1] : Array (Fin 4))[x.val]!
  invFun x := (#[2,3,0,1] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block3BaseElementLiteral4 : Equiv.Perm (Fin 4) where
  toFun x := (#[3,2,1,0] : Array (Fin 4))[x.val]!
  invFun x := (#[3,2,1,0] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block3BaseElementLiteral5 : Equiv.Perm (Fin 4) where
  toFun x := (#[1,0,3,2] : Array (Fin 4))[x.val]!
  invFun x := (#[1,0,3,2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block3BaseElementLiteral6 : Equiv.Perm (Fin 4) where
  toFun x := (#[3,0,1,2] : Array (Fin 4))[x.val]!
  invFun x := (#[1,2,3,0] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block3BaseElementLiteral7 : Equiv.Perm (Fin 4) where
  toFun x := (#[0,3,2,1] : Array (Fin 4))[x.val]!
  invFun x := (#[0,3,2,1] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def block3BaseElement (i : Fin 8) : Equiv.Perm (Fin 4) :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then block3BaseElementLiteral0 else block3BaseElementLiteral1) else (if i.val < 3 then block3BaseElementLiteral2 else block3BaseElementLiteral3)) else (if i.val < 6 then (if i.val < 5 then block3BaseElementLiteral4 else block3BaseElementLiteral5) else (if i.val < 7 then block3BaseElementLiteral6 else block3BaseElementLiteral7)))

def block3BaseGenerators (j : Fin 2) := block3BaseElement (#[1,2][j.val]!)
private def block3BaseNextTable (i : Fin 8) : Array (Fin 8) :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2] else #[3,4]) else (if i.val < 3 then #[5,0] else #[6,7])) else (if i.val < 6 then (if i.val < 5 then #[2,1] else #[7,6]) else (if i.val < 7 then #[0,5] else #[4,3])))
private def block3BaseWordTable (i : Fin 8) : List (Fin 2) :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then [] else [0]) else (if i.val < 3 then [1] else [0,0])) else (if i.val < 6 then (if i.val < 5 then [0,1] else [1,0]) else (if i.val < 7 then [0,0,0] else [0,0,1])))
private def block3BaseCayley : FiniteCayleyCertificate block3BaseGenerators 8 where
  elements := block3BaseElement
  identity := 0
  identity_eq := by decide +kernel
  next i j := (block3BaseNextTable i)[j.val]!
  next_eq := (by decide +kernel)
  words i := block3BaseWordTable i
  words_eq := (by decide +kernel)

def block3BaseCertificate := block3BaseCayley

def block3 : PermutationBlockChart (Y := Fin 4) betaGenerators where
  embedding := ⟨(fun x => (#[12,14,15,13] : Array (Fin 16))[x.val]!), by decide +kernel⟩
  images := block3Images
  intertwine := by decide +kernel

theorem block3_range : block3.hom.range =
    Subgroup.closure (Set.range block3BaseGenerators) := by
  rw [block3.hom_range]
  exact subgroup_closure_eq_of_generator_words block3.images block3BaseGenerators
    (fun i => (#[
  [0],
  [],
  [1,0],
  [0,0]
] : Array (List (Fin 2)))[i.val]!)
    (fun j => (#[
  [0],
  [0,2]
] : Array (List (Fin 4)))[j.val]!)
    (by decide +kernel) (by decide +kernel)

theorem block3_base_transitive (x y : Fin 4) :
    ∃ g : Subgroup.closure (Set.range block3BaseGenerators), (g : Equiv.Perm (Fin 4)) x = y := by
  let i : Fin 8 := ((#[
  #[0,1,2,4],
  #[5,0,1,3],
  #[2,4,0,1],
  #[1,3,5,0]
] : Array (Array (Fin 8)))[x.val]!)[y.val]!
  refine ⟨⟨block3BaseCertificate.elements i,
    (block3BaseCertificate.mem_closure_iff _).mpr ⟨i,rfl⟩⟩, ?_⟩
  have h : ∀ x y : Fin 4,
      block3BaseCertificate.elements (((#[
  #[0,1,2,4],
  #[5,0,1,3],
  #[2,4,0,1],
  #[1,3,5,0]
] : Array (Array (Fin 8)))[x.val]!)[y.val]!) x = y := by decide +kernel
  exact h x y

theorem block3_base_card :
    Nat.card (Subgroup.closure (Set.range block3BaseGenerators)) = 8 :=
  block3BaseCertificate.card_closure (by decide +kernel)

theorem physical_degree : 4 + 4 + 4 + 4 = 16 := by decide +kernel

theorem blocks1_0_disjoint : ∀ x y,
    block1.embedding x ≠ block0.embedding y := by decide +kernel

theorem blocks2_0_disjoint : ∀ x y,
    block2.embedding x ≠ block0.embedding y := by decide +kernel

theorem blocks2_1_disjoint : ∀ x y,
    block2.embedding x ≠ block1.embedding y := by decide +kernel

theorem blocks3_0_disjoint : ∀ x y,
    block3.embedding x ≠ block0.embedding y := by decide +kernel

theorem blocks3_1_disjoint : ∀ x y,
    block3.embedding x ≠ block1.embedding y := by decide +kernel

theorem blocks3_2_disjoint : ∀ x y,
    block3.embedding x ≠ block2.embedding y := by decide +kernel

theorem blocks_cover : ∀ x : Fin 16, ∃ y, block0.embedding y = x ∨ ∃ y, block1.embedding y = x ∨ ∃ y, block2.embedding y = x ∨ ∃ y, block3.embedding y = x := by decide +kernel

/-- A full literal block of positive physical size is either the
cyclic group of order four, or a degree-eight group of order above 32. -/
theorem quarter_cyclic_four_or_large_eight :
    16 ≤ 4 * 4 ∧
    ((4 = 4 ∧ IsCyclic (Subgroup.closure (Set.range block0BaseGenerators)) ∧
      Nat.card (Subgroup.closure (Set.range block0BaseGenerators)) = 4) ∨
     (4 = 8 ∧ 32 < Nat.card (Subgroup.closure (Set.range block0BaseGenerators)))) :=
  ⟨by decide +kernel, Or.inl ⟨rfl,
    subgroup_closure_single_generator_isCyclic block0BaseGenerators,
    block0_base_card⟩⟩

end BinaryChart16T1086

end SymmetricSubgroupAsymptotics
