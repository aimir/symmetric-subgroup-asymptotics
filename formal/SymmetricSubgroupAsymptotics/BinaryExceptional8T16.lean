import SymmetricSubgroupAsymptotics.FiniteGroupCertificates

/-!
# Literal transport chart 8T16

The permutation rows are the original rows from the committed binary menu,
converted to zero-based Lean notation. Cayley rows and words are untrusted
candidate witnesses; every certificate equation is checked by Lean's kernel.
No catalogue identification or external PASS output is used in a proof.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryChart8T16

private def alphaSourceLiteral0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,6,3,4,1,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,6,3,4,1,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral2 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,3,4,5,6,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,2,3,4,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral3 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,6,3,4,1,2,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,4,5,2,3,0,1,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral4 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,6,7,4,5,2,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,5,6,3,4,1,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral5 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral6 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,2,7,4,1,6,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,4,1,6,3,0,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral7 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,4,1,2,7,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,4,1,2,7,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral8 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,7,4,5,2,3,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral9 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral10 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,4,5,6,7,0,1,2] : Array (Fin 8))[x.val]!
  invFun x := (#[5,6,7,0,1,2,3,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral11 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral12 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  invFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral13 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,4,1,2,7,0,5,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,2,3,0,1,6,7,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral14 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral15 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,4,5,2,3,0,1,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,6,3,4,1,2,7,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral16 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,0,5,6,3,4,1,2] : Array (Fin 8))[x.val]!
  invFun x := (#[1,6,7,4,5,2,3,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral17 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,0,1,6,7,4,5,2] : Array (Fin 8))[x.val]!
  invFun x := (#[1,2,7,0,5,6,3,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral18 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral19 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,0,1,6,7,4,5] : Array (Fin 8))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral20 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,4,1,6,3,0,5,2] : Array (Fin 8))[x.val]!
  invFun x := (#[5,2,7,4,1,6,3,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral21 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,0,1,2,3,4,5,6] : Array (Fin 8))[x.val]!
  invFun x := (#[1,2,3,4,5,6,7,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral22 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,0,5,2,7,4,1,6] : Array (Fin 8))[x.val]!
  invFun x := (#[1,6,3,0,5,2,7,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral23 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,2,7,0,5,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,2,7,0,5,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral24 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,2,3,0,1,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,2,3,0,1,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral25 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral26 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,6,7,0,1,2,3,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,4,5,6,7,0,1,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral27 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral28 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral29 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,7,0,5,6,3,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,0,1,6,7,4,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral30 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,2,3,0,1,6,7,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,4,1,2,7,0,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral31 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,6,3,0,5,2,7,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,0,5,2,7,4,1,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSource (i : Fin 32) : Equiv.Perm (Fin 8) :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then alphaSourceLiteral0 else alphaSourceLiteral1) else (if i.val < 3 then alphaSourceLiteral2 else alphaSourceLiteral3)) else (if i.val < 6 then (if i.val < 5 then alphaSourceLiteral4 else alphaSourceLiteral5) else (if i.val < 7 then alphaSourceLiteral6 else alphaSourceLiteral7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then alphaSourceLiteral8 else alphaSourceLiteral9) else (if i.val < 11 then alphaSourceLiteral10 else alphaSourceLiteral11)) else (if i.val < 14 then (if i.val < 13 then alphaSourceLiteral12 else alphaSourceLiteral13) else (if i.val < 15 then alphaSourceLiteral14 else alphaSourceLiteral15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then alphaSourceLiteral16 else alphaSourceLiteral17) else (if i.val < 19 then alphaSourceLiteral18 else alphaSourceLiteral19)) else (if i.val < 22 then (if i.val < 21 then alphaSourceLiteral20 else alphaSourceLiteral21) else (if i.val < 23 then alphaSourceLiteral22 else alphaSourceLiteral23))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then alphaSourceLiteral24 else alphaSourceLiteral25) else (if i.val < 27 then alphaSourceLiteral26 else alphaSourceLiteral27)) else (if i.val < 30 then (if i.val < 29 then alphaSourceLiteral28 else alphaSourceLiteral29) else (if i.val < 31 then alphaSourceLiteral30 else alphaSourceLiteral31)))))

private def alphaTargetLiteral0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,7,9,10,0,12,13,1,14,2,3,15,5,6,8,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,7,9,10,0,12,13,1,14,2,3,15,5,6,8,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,5,7,6,0,9,8,12,11,13,4,3,14,15,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,0,1,12,11,2,4,3,7,6,15,9,8,10,13,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral3 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,9,12,1,13,4,2,14,5,15,6,0,10,8,11,3] : Array (Fin 16))[x.val]!
  invFun x := (#[11,3,6,15,5,8,10,0,13,1,12,14,2,4,7,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral4 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,8,11,13,1,3,14,2,15,5,7,10,0,9,12,4] : Array (Fin 16))[x.val]!
  invFun x := (#[12,4,7,5,15,9,0,10,1,13,11,2,14,3,6,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral5 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,5,0,8,9,1,11,12,3,4,14,6,7,15,10,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,5,0,8,9,1,11,12,3,4,14,6,7,15,10,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral6 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,14,15,6,7,10,8,9,11,12,1,3,4,2,5,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,10,13,11,12,14,3,4,6,7,5,8,9,0,1,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral7 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,12,4,14,2,7,15,5,10,0,8,13,1,11,3,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,12,4,14,2,7,15,5,10,0,8,13,1,11,3,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral8 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,11,3,2,14,6,5,15,0,10,9,1,13,12,4,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,11,3,2,14,6,5,15,0,10,9,1,13,12,4,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral9 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,0,1,12,11,2,4,3,7,6,15,9,8,10,13,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,5,7,6,0,9,8,12,11,13,4,3,14,15,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral10 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,10,9,8,13,12,11,4,3,2,7,6,5,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,10,9,8,13,12,11,4,3,2,7,6,5,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral11 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,4,7,5,15,9,0,10,1,13,11,2,14,3,6,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,8,11,13,1,3,14,2,15,5,7,10,0,9,12,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral12 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,3,6,15,5,8,10,0,13,1,12,14,2,4,7,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,9,12,1,13,4,2,14,5,15,6,0,10,8,11,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral13 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,10,13,11,12,14,3,4,6,7,5,8,9,0,1,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,14,15,6,7,10,8,9,11,12,1,3,4,2,5,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral14 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,6,8,0,10,11,1,13,2,14,4,5,15,7,9,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,6,8,0,10,11,1,13,2,14,4,5,15,7,9,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral15 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,13,14,4,3,15,7,6,9,8,0,12,11,1,2,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,13,14,4,3,15,7,6,9,8,0,12,11,1,2,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTarget (i : Fin 32) : Equiv.Perm (Fin 16) :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then alphaTargetLiteral0 else alphaTargetLiteral1) else (if i.val < 3 then alphaTargetLiteral2 else alphaTargetLiteral3)) else (if i.val < 6 then (if i.val < 5 then alphaTargetLiteral4 else alphaTargetLiteral5) else (if i.val < 7 then alphaTargetLiteral6 else alphaTargetLiteral7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then alphaTargetLiteral8 else alphaTargetLiteral7) else (if i.val < 11 then alphaTargetLiteral9 else alphaTargetLiteral10)) else (if i.val < 14 then (if i.val < 13 then alphaTargetLiteral5 else alphaTargetLiteral11) else (if i.val < 15 then alphaTargetLiteral10 else alphaTargetLiteral12)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then alphaTargetLiteral11 else alphaTargetLiteral12) else (if i.val < 19 then alphaTargetLiteral0 else alphaTargetLiteral8)) else (if i.val < 22 then (if i.val < 21 then alphaTargetLiteral13 else alphaTargetLiteral9) else (if i.val < 23 then alphaTargetLiteral13 else alphaTargetLiteral1))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then alphaTargetLiteral14 else alphaTargetLiteral14) else (if i.val < 27 then alphaTargetLiteral2 else alphaTargetLiteral15)) else (if i.val < 30 then (if i.val < 29 then alphaTargetLiteral15 else alphaTargetLiteral3) else (if i.val < 31 then alphaTargetLiteral4 else alphaTargetLiteral6)))))

def alphaGenerators (j : Fin 2) := alphaSource (#[1,2][j.val]!)
def alphaImages (j : Fin 2) := alphaTarget (#[1,2][j.val]!)
private def alphaNextTable (i : Fin 32) : Array (Fin 32) :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2] else #[0,3]) else (if i.val < 3 then #[4,5] else #[6,7])) else (if i.val < 6 then (if i.val < 5 then #[2,8] else #[9,10]) else (if i.val < 7 then #[3,11] else #[12,13]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[14,15] else #[5,16]) else (if i.val < 11 then #[17,18] else #[19,20])) else (if i.val < 14 then (if i.val < 13 then #[7,21] else #[22,23]) else (if i.val < 15 then #[8,22] else #[21,24])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[20,1] else #[10,25]) else (if i.val < 19 then #[23,26] else #[11,17])) else (if i.val < 22 then (if i.val < 21 then #[16,27] else #[15,0]) else (if i.val < 23 then #[13,28] else #[18,29]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[27,30] else #[28,4]) else (if i.val < 27 then #[30,12] else #[24,31])) else (if i.val < 30 then (if i.val < 29 then #[25,6] else #[31,9]) else (if i.val < 31 then #[26,19] else #[29,14])))))
private def alphaWordTable (i : Fin 32) : List (Fin 2) :=
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then [] else [0]) else (if i.val < 3 then [1] else [0,1])) else (if i.val < 6 then (if i.val < 5 then [1,0] else [1,1]) else (if i.val < 7 then [0,1,0] else [0,1,1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then [1,0,1] else [1,1,0]) else (if i.val < 11 then [1,1,1] else [0,1,0,1])) else (if i.val < 14 then (if i.val < 13 then [0,1,1,0] else [0,1,1,1]) else (if i.val < 15 then [1,0,1,0] else [1,0,1,1])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then [1,1,0,1] else [1,1,1,0]) else (if i.val < 19 then [1,1,1,1] else [0,1,0,1,0])) else (if i.val < 22 then (if i.val < 21 then [0,1,0,1,1] else [0,1,1,0,1]) else (if i.val < 23 then [0,1,1,1,0] else [0,1,1,1,1]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then [1,0,1,1,1] else [1,1,1,0,1]) else (if i.val < 27 then [1,1,1,1,1] else [0,1,0,1,1,1])) else (if i.val < 30 then (if i.val < 29 then [0,1,1,1,0,1] else [0,1,1,1,1,1]) else (if i.val < 31 then [1,0,1,1,1,1] else [0,1,0,1,1,1,1])))))
private def alphaCayley : FiniteCayleyCertificate (fun j => (alphaGenerators j, alphaImages j)) 32 where
  elements := (fun i => (alphaSource i, alphaTarget i))
  identity := 0
  identity_eq := by decide +kernel
  next i j := (alphaNextTable i)[j.val]!
  next_eq := (by decide +kernel)
  words i := alphaWordTable i
  words_eq := (by decide +kernel)

def alphaCertificate : FiniteHomCertificate alphaGenerators alphaImages 32 where
  cayley := alphaCayley
  first_kernel := (by decide +kernel)

private def betaSourceLiteral0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral1 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,7,4,5,6,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,6,3,4,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral2 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,7,4,5,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral3 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral4 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,7,0,5,6,3,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,0,1,6,7,4,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral5 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,3,4,5,6,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,1,2,3,4,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral6 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,0,1,6,3,4,5,2] : Array (Fin 8))[x.val]!
  invFun x := (#[1,2,7,4,5,6,3,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral7 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,1,6,3,4,5] : Array (Fin 8))[x.val]!
  invFun x := (#[2,3,0,5,6,7,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral8 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,4,5,6,3,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,0,5,2,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral9 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,0,5,6,7,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,1,6,3,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral10 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,3,0,5,6,7,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,0,1,2,7,4,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral11 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,0,1,2,3,4,5,6] : Array (Fin 8))[x.val]!
  invFun x := (#[1,2,3,4,5,6,7,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral12 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,0,5,6,3,4,1,2] : Array (Fin 8))[x.val]!
  invFun x := (#[1,6,7,4,5,2,3,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral13 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,4,1,6,3,0,5,2] : Array (Fin 8))[x.val]!
  invFun x := (#[5,2,7,4,1,6,3,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral14 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral15 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,0,1,6,7,4,5,2] : Array (Fin 8))[x.val]!
  invFun x := (#[1,2,7,0,5,6,3,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral16 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,0,1,6,7,4,5] : Array (Fin 8))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral17 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral18 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,6,3,4,5,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,6,3,4,5,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral19 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,2,3,4,1,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,2,3,4,1,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral20 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,0,5,2,3,4,1,6] : Array (Fin 8))[x.val]!
  invFun x := (#[1,6,3,4,5,2,7,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral21 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,2,3,0,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,2,3,0,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral22 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,4,1,2,3,0,5,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,2,3,4,1,6,7,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral23 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,4,5,6,3,0,1,2] : Array (Fin 8))[x.val]!
  invFun x := (#[5,6,7,4,1,2,3,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral24 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,0,1,2,7,4,5,6] : Array (Fin 8))[x.val]!
  invFun x := (#[1,2,3,0,5,6,7,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral25 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,0,5,6,7,4,1,2] : Array (Fin 8))[x.val]!
  invFun x := (#[1,6,7,0,5,2,3,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral26 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,4,1,6,7,0,5,2] : Array (Fin 8))[x.val]!
  invFun x := (#[5,2,7,0,1,6,3,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral27 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,4,1,6,7,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,0,1,2,7,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral28 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,6,7,4,5,2,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,5,6,3,4,1,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral29 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,6,7,4,5,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral30 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,2,7,4,1,6,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,4,1,6,3,0,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral31 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral32 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,6,3,4,1,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,6,3,4,1,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral33 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,2,7,0,5,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,2,7,0,5,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral34 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral35 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,2,3,0,1,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,2,3,0,1,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral36 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,4,5,2,3,0,1,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,6,3,4,1,2,7,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral37 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,0,5,2,7,4,1,6] : Array (Fin 8))[x.val]!
  invFun x := (#[1,6,3,0,5,2,7,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral38 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,4,1,2,7,0,5,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,2,3,0,1,6,7,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral39 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,4,5,6,7,0,1,2] : Array (Fin 8))[x.val]!
  invFun x := (#[5,6,7,0,1,2,3,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral40 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,7,0,5,2,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,4,5,6,3,0,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral41 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,6,7,0,5,2,3,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,0,5,6,7,4,1,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral42 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,6,3,4,5,2,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,0,5,2,3,4,1,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral43 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,2,7,0,1,6,3,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,4,1,6,7,0,5,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral44 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,2,3,4,1,6,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,4,1,2,3,0,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral45 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,6,7,4,1,2,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,4,5,6,3,0,1,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral46 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,6,7,4,1,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,6,7,4,1,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral47 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,6,7,0,5,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,6,7,0,5,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral48 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,2,7,0,1,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,2,7,0,1,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral49 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,6,3,0,1,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,6,3,0,1,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral50 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,4,5,2,7,0,1,6] : Array (Fin 8))[x.val]!
  invFun x := (#[5,6,3,0,1,2,7,4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral51 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,7,0,1,2,3,4,5] : Array (Fin 8))[x.val]!
  invFun x := (#[2,3,4,5,6,7,0,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral52 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,7,4,5,2,3,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral53 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,0,5,2,7,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,4,1,6,3,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral54 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,6,3,0,5,2,7,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,0,5,2,7,4,1,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral55 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,2,3,0,1,6,7,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,4,1,2,7,0,5,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral56 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,6,7,0,1,2,3,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,4,5,6,7,0,1,2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral57 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,6,3,4,1,2,7,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,4,5,2,3,0,1,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral58 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral59 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,7,4,1,2,3,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,4,5,2,7,0,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral60 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,0,1,2,7,4,5] : Array (Fin 8))[x.val]!
  invFun x := (#[2,3,4,1,6,7,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral61 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,4,5,2,7,0,1] : Array (Fin 8))[x.val]!
  invFun x := (#[6,7,4,1,2,3,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral62 : Equiv.Perm (Fin 8) where
  toFun x := (#[5,6,3,0,1,2,7,4] : Array (Fin 8))[x.val]!
  invFun x := (#[3,4,5,2,7,0,1,6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral63 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,3,4,1,2,7,0,5] : Array (Fin 8))[x.val]!
  invFun x := (#[6,3,4,1,2,7,0,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSource (i : Fin 64) : Equiv.Perm (Fin 8) :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then betaSourceLiteral0 else betaSourceLiteral1) else (if i.val < 3 then betaSourceLiteral2 else betaSourceLiteral3)) else (if i.val < 6 then (if i.val < 5 then betaSourceLiteral4 else betaSourceLiteral5) else (if i.val < 7 then betaSourceLiteral6 else betaSourceLiteral7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then betaSourceLiteral8 else betaSourceLiteral9) else (if i.val < 11 then betaSourceLiteral10 else betaSourceLiteral11)) else (if i.val < 14 then (if i.val < 13 then betaSourceLiteral12 else betaSourceLiteral13) else (if i.val < 15 then betaSourceLiteral14 else betaSourceLiteral15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then betaSourceLiteral16 else betaSourceLiteral17) else (if i.val < 19 then betaSourceLiteral18 else betaSourceLiteral19)) else (if i.val < 22 then (if i.val < 21 then betaSourceLiteral20 else betaSourceLiteral21) else (if i.val < 23 then betaSourceLiteral22 else betaSourceLiteral23))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then betaSourceLiteral24 else betaSourceLiteral25) else (if i.val < 27 then betaSourceLiteral26 else betaSourceLiteral27)) else (if i.val < 30 then (if i.val < 29 then betaSourceLiteral28 else betaSourceLiteral29) else (if i.val < 31 then betaSourceLiteral30 else betaSourceLiteral31))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then betaSourceLiteral32 else betaSourceLiteral33) else (if i.val < 35 then betaSourceLiteral34 else betaSourceLiteral35)) else (if i.val < 38 then (if i.val < 37 then betaSourceLiteral36 else betaSourceLiteral37) else (if i.val < 39 then betaSourceLiteral38 else betaSourceLiteral39))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then betaSourceLiteral40 else betaSourceLiteral41) else (if i.val < 43 then betaSourceLiteral42 else betaSourceLiteral43)) else (if i.val < 46 then (if i.val < 45 then betaSourceLiteral44 else betaSourceLiteral45) else (if i.val < 47 then betaSourceLiteral46 else betaSourceLiteral47)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then betaSourceLiteral48 else betaSourceLiteral49) else (if i.val < 51 then betaSourceLiteral50 else betaSourceLiteral51)) else (if i.val < 54 then (if i.val < 53 then betaSourceLiteral52 else betaSourceLiteral53) else (if i.val < 55 then betaSourceLiteral54 else betaSourceLiteral55))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then betaSourceLiteral56 else betaSourceLiteral57) else (if i.val < 59 then betaSourceLiteral58 else betaSourceLiteral59)) else (if i.val < 62 then (if i.val < 61 then betaSourceLiteral60 else betaSourceLiteral61) else (if i.val < 63 then betaSourceLiteral62 else betaSourceLiteral63))))))

private def betaTargetLiteral0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,3,6,15,5,8,10,0,13,1,12,14,2,4,7,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,9,12,1,13,4,2,14,5,15,6,0,10,8,11,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,12,4,14,2,7,15,5,10,0,8,13,1,11,3,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,12,4,14,2,7,15,5,10,0,8,13,1,11,3,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral3 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,10,9,8,13,12,11,4,3,2,7,6,5,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,10,9,8,13,12,11,4,3,2,7,6,5,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral4 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,5,7,6,0,9,8,12,11,13,4,3,14,15,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,0,1,12,11,2,4,3,7,6,15,9,8,10,13,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral5 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,14,15,6,7,10,8,9,11,12,1,3,4,2,5,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,10,13,11,12,14,3,4,6,7,5,8,9,0,1,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral6 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,9,12,1,13,4,2,14,5,15,6,0,10,8,11,3] : Array (Fin 16))[x.val]!
  invFun x := (#[11,3,6,15,5,8,10,0,13,1,12,14,2,4,7,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral7 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,6,8,0,10,11,1,13,2,14,4,5,15,7,9,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,6,8,0,10,11,1,13,2,14,4,5,15,7,9,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral8 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,7,9,10,0,12,13,1,14,2,3,15,5,6,8,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,7,9,10,0,12,13,1,14,2,3,15,5,6,8,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral9 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,4,7,5,15,9,0,10,1,13,11,2,14,3,6,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,8,11,13,1,3,14,2,15,5,7,10,0,9,12,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral10 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,10,13,11,12,14,3,4,6,7,5,8,9,0,1,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,14,15,6,7,10,8,9,11,12,1,3,4,2,5,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral11 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,0,1,12,11,2,4,3,7,6,15,9,8,10,13,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,5,7,6,0,9,8,12,11,13,4,3,14,15,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral12 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,5,0,8,9,1,11,12,3,4,14,6,7,15,10,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,5,0,8,9,1,11,12,3,4,14,6,7,15,10,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral13 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,11,3,2,14,6,5,15,0,10,9,1,13,12,4,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,11,3,2,14,6,5,15,0,10,9,1,13,12,4,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral14 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,8,11,13,1,3,14,2,15,5,7,10,0,9,12,4] : Array (Fin 16))[x.val]!
  invFun x := (#[12,4,7,5,15,9,0,10,1,13,11,2,14,3,6,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral15 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,13,14,4,3,15,7,6,9,8,0,12,11,1,2,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,13,14,4,3,15,7,6,9,8,0,12,11,1,2,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTarget (i : Fin 64) : Equiv.Perm (Fin 16) :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then betaTargetLiteral0 else betaTargetLiteral1) else (if i.val < 3 then betaTargetLiteral2 else betaTargetLiteral3)) else (if i.val < 6 then (if i.val < 5 then betaTargetLiteral4 else betaTargetLiteral5) else (if i.val < 7 then betaTargetLiteral6 else betaTargetLiteral7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then betaTargetLiteral8 else betaTargetLiteral7) else (if i.val < 11 then betaTargetLiteral9 else betaTargetLiteral10)) else (if i.val < 14 then (if i.val < 13 then betaTargetLiteral11 else betaTargetLiteral10) else (if i.val < 15 then betaTargetLiteral12 else betaTargetLiteral11)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then betaTargetLiteral3 else betaTargetLiteral12) else (if i.val < 19 then betaTargetLiteral13 else betaTargetLiteral2)) else (if i.val < 22 then (if i.val < 21 then betaTargetLiteral14 else betaTargetLiteral13) else (if i.val < 23 then betaTargetLiteral6 else betaTargetLiteral14))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then betaTargetLiteral14 else betaTargetLiteral6) else (if i.val < 27 then betaTargetLiteral14 else betaTargetLiteral8)) else (if i.val < 30 then (if i.val < 29 then betaTargetLiteral4 else betaTargetLiteral15) else (if i.val < 31 then betaTargetLiteral5 else betaTargetLiteral0))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then betaTargetLiteral15 else betaTargetLiteral15) else (if i.val < 35 then betaTargetLiteral0 else betaTargetLiteral15)) else (if i.val < 38 then (if i.val < 37 then betaTargetLiteral11 else betaTargetLiteral10) else (if i.val < 39 then betaTargetLiteral11 else betaTargetLiteral10))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then betaTargetLiteral8 else betaTargetLiteral1) else (if i.val < 43 then betaTargetLiteral9 else betaTargetLiteral9)) else (if i.val < 46 then (if i.val < 45 then betaTargetLiteral1 else betaTargetLiteral9) else (if i.val < 47 then betaTargetLiteral13 else betaTargetLiteral2)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then betaTargetLiteral13 else betaTargetLiteral2) else (if i.val < 51 then betaTargetLiteral6 else betaTargetLiteral12)) else (if i.val < 54 then (if i.val < 53 then betaTargetLiteral3 else betaTargetLiteral12) else (if i.val < 55 then betaTargetLiteral5 else betaTargetLiteral4))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then betaTargetLiteral5 else betaTargetLiteral4) else (if i.val < 59 then betaTargetLiteral0 else betaTargetLiteral7)) else (if i.val < 62 then (if i.val < 61 then betaTargetLiteral8 else betaTargetLiteral7) else (if i.val < 63 then betaTargetLiteral1 else betaTargetLiteral3))))))

def betaGenerators (j : Fin 2) := betaSource (#[1,2][j.val]!)
def betaImages (j : Fin 2) := betaTarget (#[1,2][j.val]!)
private def betaNextTable (i : Fin 64) : Array (Fin 64) :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2] else #[3,4]) else (if i.val < 3 then #[5,0] else #[6,7])) else (if i.val < 6 then (if i.val < 5 then #[8,1] else #[9,10]) else (if i.val < 7 then #[0,11] else #[12,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[13,14] else #[15,16]) else (if i.val < 11 then #[17,5] else #[18,6])) else (if i.val < 14 then (if i.val < 13 then #[19,20] else #[21,22]) else (if i.val < 15 then #[23,8] else #[2,24])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[25,9] else #[26,27]) else (if i.val < 19 then #[28,29] else #[30,31])) else (if i.val < 22 then (if i.val < 21 then #[32,12] else #[4,33]) else (if i.val < 23 then #[34,13] else #[35,36]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[29,15] else #[31,37]) else (if i.val < 27 then #[33,38] else #[39,17])) else (if i.val < 30 then (if i.val < 29 then #[40,41] else #[42,18]) else (if i.val < 31 then #[7,43] else #[44,19]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[45,46] else #[10,21]) else (if i.val < 35 then #[41,47] else #[43,48])) else (if i.val < 38 then (if i.val < 37 then #[49,23] else #[46,25]) else (if i.val < 39 then #[47,26] else #[48,50]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[11,51] else #[52,28]) else (if i.val < 43 then #[53,54] else #[14,30])) else (if i.val < 46 then (if i.val < 45 then #[16,55] else #[51,56]) else (if i.val < 47 then #[57,32] else #[54,34])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[55,35] else #[56,58]) else (if i.val < 51 then #[58,39] else #[20,40])) else (if i.val < 54 then (if i.val < 53 then #[22,59] else #[24,60]) else (if i.val < 55 then #[61,42] else #[27,44]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[59,45] else #[60,62]) else (if i.val < 59 then #[62,49] else #[36,52])) else (if i.val < 62 then (if i.val < 61 then #[37,53] else #[38,63]) else (if i.val < 63 then #[63,57] else #[50,61]))))))
private def betaWordTable (i : Fin 64) : List (Fin 2) :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then [] else [0]) else (if i.val < 3 then [1] else [0,0])) else (if i.val < 6 then (if i.val < 5 then [0,1] else [1,0]) else (if i.val < 7 then [0,0,0] else [0,0,1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then [0,1,0] else [1,0,0]) else (if i.val < 11 then [1,0,1] else [0,0,0,1])) else (if i.val < 14 then (if i.val < 13 then [0,0,1,0] else [0,1,0,0]) else (if i.val < 15 then [0,1,0,1] else [1,0,0,0])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then [1,0,0,1] else [1,0,1,0]) else (if i.val < 19 then [0,0,0,1,0] else [0,0,1,0,0])) else (if i.val < 22 then (if i.val < 21 then [0,0,1,0,1] else [0,1,0,0,0]) else (if i.val < 23 then [0,1,0,0,1] else [0,1,0,1,0]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then [1,0,0,0,1] else [1,0,0,1,0]) else (if i.val < 27 then [1,0,1,0,0] else [1,0,1,0,1])) else (if i.val < 30 then (if i.val < 29 then [0,0,0,1,0,0] else [0,0,0,1,0,1]) else (if i.val < 31 then [0,0,1,0,0,0] else [0,0,1,0,0,1]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then [0,0,1,0,1,0] else [0,1,0,0,0,1]) else (if i.val < 35 then [0,1,0,0,1,0] else [0,1,0,1,0,0])) else (if i.val < 38 then (if i.val < 37 then [0,1,0,1,0,1] else [1,0,0,1,0,1]) else (if i.val < 39 then [1,0,1,0,0,1] else [1,0,1,0,1,0]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then [0,0,0,1,0,0,0] else [0,0,0,1,0,0,1]) else (if i.val < 43 then [0,0,0,1,0,1,0] else [0,0,1,0,0,0,1])) else (if i.val < 46 then (if i.val < 45 then [0,0,1,0,0,1,0] else [0,0,1,0,1,0,0]) else (if i.val < 47 then [0,0,1,0,1,0,1] else [0,1,0,0,1,0,1])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then [0,1,0,1,0,0,1] else [0,1,0,1,0,1,0]) else (if i.val < 51 then [1,0,1,0,1,0,1] else [0,0,0,1,0,0,0,1])) else (if i.val < 54 then (if i.val < 53 then [0,0,0,1,0,0,1,0] else [0,0,0,1,0,1,0,0]) else (if i.val < 55 then [0,0,0,1,0,1,0,1] else [0,0,1,0,0,1,0,1]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then [0,0,1,0,1,0,0,1] else [0,0,1,0,1,0,1,0]) else (if i.val < 59 then [0,1,0,1,0,1,0,1] else [0,0,0,1,0,0,1,0,1])) else (if i.val < 62 then (if i.val < 61 then [0,0,0,1,0,1,0,0,1] else [0,0,0,1,0,1,0,1,0]) else (if i.val < 63 then [0,0,1,0,1,0,1,0,1] else [0,0,0,1,0,1,0,1,0,1]))))))
private def betaCayley : FiniteCayleyCertificate (fun j => (betaGenerators j, betaImages j)) 64 where
  elements := (fun i => (betaSource i, betaTarget i))
  identity := 0
  identity_eq := by decide +kernel
  next i j := (betaNextTable i)[j.val]!
  next_eq := (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))
  words i := betaWordTable i
  words_eq := (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))

def betaCertificate : FiniteHomCertificate betaGenerators betaImages 64 where
  cayley := betaCayley
  first_kernel := (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))

private def quotientElementLiteral0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,5,7,6,0,9,8,12,11,13,4,3,14,15,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,0,1,12,11,2,4,3,7,6,15,9,8,10,13,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,6,8,0,10,11,1,13,2,14,4,5,15,7,9,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,6,8,0,10,11,1,13,2,14,4,5,15,7,9,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,7,9,10,0,12,13,1,14,2,3,15,5,6,8,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,7,9,10,0,12,13,1,14,2,3,15,5,6,8,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral4 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,5,0,8,9,1,11,12,3,4,14,6,7,15,10,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,5,0,8,9,1,11,12,3,4,14,6,7,15,10,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral5 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,9,12,1,13,4,2,14,5,15,6,0,10,8,11,3] : Array (Fin 16))[x.val]!
  invFun x := (#[11,3,6,15,5,8,10,0,13,1,12,14,2,4,7,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral6 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,8,11,13,1,3,14,2,15,5,7,10,0,9,12,4] : Array (Fin 16))[x.val]!
  invFun x := (#[12,4,7,5,15,9,0,10,1,13,11,2,14,3,6,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral7 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,13,14,4,3,15,7,6,9,8,0,12,11,1,2,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,13,14,4,3,15,7,6,9,8,0,12,11,1,2,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral8 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,0,1,12,11,2,4,3,7,6,15,9,8,10,13,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,5,7,6,0,9,8,12,11,13,4,3,14,15,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral9 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,11,3,2,14,6,5,15,0,10,9,1,13,12,4,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,11,3,2,14,6,5,15,0,10,9,1,13,12,4,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral10 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,12,4,14,2,7,15,5,10,0,8,13,1,11,3,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,12,4,14,2,7,15,5,10,0,8,13,1,11,3,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral11 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,14,15,6,7,10,8,9,11,12,1,3,4,2,5,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,10,13,11,12,14,3,4,6,7,5,8,9,0,1,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral12 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,4,7,5,15,9,0,10,1,13,11,2,14,3,6,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,8,11,13,1,3,14,2,15,5,7,10,0,9,12,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral13 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,3,6,15,5,8,10,0,13,1,12,14,2,4,7,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,9,12,1,13,4,2,14,5,15,6,0,10,8,11,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral14 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,10,9,8,13,12,11,4,3,2,7,6,5,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,10,9,8,13,12,11,4,3,2,7,6,5,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral15 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,10,13,11,12,14,3,4,6,7,5,8,9,0,1,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,14,15,6,7,10,8,9,11,12,1,3,4,2,5,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElement (i : Fin 16) : Equiv.Perm (Fin 16) :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then quotientElementLiteral0 else quotientElementLiteral1) else (if i.val < 3 then quotientElementLiteral2 else quotientElementLiteral3)) else (if i.val < 6 then (if i.val < 5 then quotientElementLiteral4 else quotientElementLiteral5) else (if i.val < 7 then quotientElementLiteral6 else quotientElementLiteral7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then quotientElementLiteral8 else quotientElementLiteral9) else (if i.val < 11 then quotientElementLiteral10 else quotientElementLiteral11)) else (if i.val < 14 then (if i.val < 13 then quotientElementLiteral12 else quotientElementLiteral13) else (if i.val < 15 then quotientElementLiteral14 else quotientElementLiteral15))))

def quotientGenerators (j : Fin 3) := quotientElement (#[1,2,3][j.val]!)
private def quotientNextTable (i : Fin 16) : Array (Fin 16) :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3] else #[4,5,6]) else (if i.val < 3 then #[6,0,7] else #[5,7,0])) else (if i.val < 6 then (if i.val < 5 then #[8,9,10] else #[10,1,11]) else (if i.val < 7 then #[9,11,1] else #[11,3,2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[0,12,13] else #[13,4,14]) else (if i.val < 11 then #[12,14,4] else #[14,6,5])) else (if i.val < 14 then (if i.val < 13 then #[3,8,15] else #[2,15,8]) else (if i.val < 15 then #[15,10,9] else #[7,13,12]))))
private def quotientWordTable (i : Fin 16) : List (Fin 3) :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then [] else [0]) else (if i.val < 3 then [1] else [2])) else (if i.val < 6 then (if i.val < 5 then [0,0] else [0,1]) else (if i.val < 7 then [0,2] else [1,2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then [0,0,0] else [0,0,1]) else (if i.val < 11 then [0,0,2] else [0,1,2])) else (if i.val < 14 then (if i.val < 13 then [0,0,0,1] else [0,0,0,2]) else (if i.val < 15 then [0,0,1,2] else [0,0,0,1,2]))))
private def quotientCayley : FiniteCayleyCertificate quotientGenerators 16 where
  elements := quotientElement
  identity := 0
  identity_eq := by decide +kernel
  next i j := (quotientNextTable i)[j.val]!
  next_eq := (by decide +kernel)
  words i := quotientWordTable i
  words_eq := (by decide +kernel)

def quotientCertificate := quotientCayley

private def axisElementLiteral0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def axisElementLiteral1 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def axisElement (i : Fin 2) : Equiv.Perm (Fin 8) :=
  (if i.val < 1 then axisElementLiteral0 else axisElementLiteral1)

def axisGenerators (j : Fin 1) := axisElement (#[1][j.val]!)
private def axisNextTable (i : Fin 2) : Array (Fin 2) :=
  (if i.val < 1 then #[1] else #[0])
private def axisWordTable (i : Fin 2) : List (Fin 1) :=
  (if i.val < 1 then [] else [0])
private def axisCayley : FiniteCayleyCertificate axisGenerators 2 where
  elements := axisElement
  identity := 0
  identity_eq := by decide +kernel
  next i j := (axisNextTable i)[j.val]!
  next_eq := (by decide +kernel)
  words i := axisWordTable i
  words_eq := (by decide +kernel)

def axisCertificate := axisCayley

private def coverKernelElementLiteral0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def coverKernelElementLiteral1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,5,2,7,4,1,6,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def coverKernelElementLiteral2 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  invFun x := (#[4,1,6,3,0,5,2,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def coverKernelElementLiteral3 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def coverKernelElement (i : Fin 4) : Equiv.Perm (Fin 8) :=
  (if i.val < 2 then (if i.val < 1 then coverKernelElementLiteral0 else coverKernelElementLiteral1) else (if i.val < 3 then coverKernelElementLiteral2 else coverKernelElementLiteral3))

def coverKernelGenerators (j : Fin 2) := coverKernelElement (#[1,2][j.val]!)
private def coverKernelNextTable (i : Fin 4) : Array (Fin 4) :=
  (if i.val < 2 then (if i.val < 1 then #[1,2] else #[0,3]) else (if i.val < 3 then #[3,0] else #[2,1]))
private def coverKernelWordTable (i : Fin 4) : List (Fin 2) :=
  (if i.val < 2 then (if i.val < 1 then [] else [0]) else (if i.val < 3 then [1] else [0,1]))
private def coverKernelCayley : FiniteCayleyCertificate coverKernelGenerators 4 where
  elements := coverKernelElement
  identity := 0
  identity_eq := by decide +kernel
  next i j := (coverKernelNextTable i)[j.val]!
  next_eq := (by decide +kernel)
  words i := coverKernelWordTable i
  words_eq := (by decide +kernel)

def coverKernelCertificate := coverKernelCayley

theorem alpha_range : alphaCertificate.hom.range =
    Subgroup.closure (Set.range quotientGenerators) :=
  alphaCertificate.hom_range_eq_of_rows quotientCertificate
    (fun i => (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 3) else (if i.val < 3 then 1 else 5)) else (if i.val < 6 then (if i.val < 5 then 6 else 4) else (if i.val < 7 then 11 else 10))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 9 else 10) else (if i.val < 11 then 8 else 14)) else (if i.val < 14 then (if i.val < 13 then 4 else 12) else (if i.val < 15 then 14 else 13)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 12 else 13) else (if i.val < 19 then 0 else 9)) else (if i.val < 22 then (if i.val < 21 then 15 else 8) else (if i.val < 23 then 15 else 3))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 2 else 2) else (if i.val < 27 then 1 else 7)) else (if i.val < 30 then (if i.val < 29 then 7 else 5) else (if i.val < 31 then 6 else 11))))))
    (fun j => (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 2) else (if j.val < 3 then 24 else 1)) else (if j.val < 6 then (if j.val < 5 then 5 else 3) else (if j.val < 7 then 4 else 27))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 10 else 8) else (if j.val < 11 then 7 else 6)) else (if j.val < 14 then (if j.val < 13 then 13 else 15) else (if j.val < 15 then 11 else 20)))))
    (by decide +kernel) (by decide +kernel)

theorem alpha_kernel : alphaCertificate.hom.ker.map
    (Subgroup.closure (Set.range alphaGenerators)).subtype =
      Subgroup.closure (Set.range axisGenerators) :=
  alphaCertificate.kernel_image_eq_of_rows axisCertificate
    (fun i => (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 0) else (if i.val < 7 then 0 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 0) else (if i.val < 11 then 0 else 0)) else (if i.val < 14 then (if i.val < 13 then 0 else 0) else (if i.val < 15 then 0 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 0) else (if i.val < 19 then 1 else 0)) else (if i.val < 22 then (if i.val < 21 then 0 else 0) else (if i.val < 23 then 0 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 0) else (if i.val < 27 then 0 else 0)) else (if i.val < 30 then (if i.val < 29 then 0 else 0) else (if i.val < 31 then 0 else 0))))))
    (fun j => (if j.val < 1 then 0 else 18))
    (by decide +kernel) (by decide +kernel)

theorem beta_range : betaCertificate.hom.range =
    Subgroup.closure (Set.range quotientGenerators) :=
  betaCertificate.hom_range_eq_of_rows quotientCertificate
    (fun i => (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 13) else (if i.val < 3 then 10 else 14)) else (if i.val < 6 then (if i.val < 5 then 1 else 11) else (if i.val < 7 then 5 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 2) else (if i.val < 11 then 12 else 15)) else (if i.val < 14 then (if i.val < 13 then 8 else 15) else (if i.val < 15 then 4 else 8)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 14 else 4) else (if i.val < 19 then 9 else 10)) else (if i.val < 22 then (if i.val < 21 then 6 else 9) else (if i.val < 23 then 5 else 6))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 6 else 5) else (if i.val < 27 then 6 else 3)) else (if i.val < 30 then (if i.val < 29 then 1 else 7) else (if i.val < 31 then 11 else 0))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 7 else 7) else (if i.val < 35 then 0 else 7)) else (if i.val < 38 then (if i.val < 37 then 8 else 15) else (if i.val < 39 then 8 else 15))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 3 else 13) else (if i.val < 43 then 12 else 12)) else (if i.val < 46 then (if i.val < 45 then 13 else 12) else (if i.val < 47 then 9 else 10)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 9 else 10) else (if i.val < 51 then 5 else 4)) else (if i.val < 54 then (if i.val < 53 then 14 else 4) else (if i.val < 55 then 11 else 1))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 11 else 1) else (if i.val < 59 then 0 else 2)) else (if i.val < 62 then (if i.val < 61 then 3 else 2) else (if i.val < 63 then 13 else 14)))))))
    (fun j => (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 4) else (if j.val < 3 then 7 else 8)) else (if j.val < 6 then (if j.val < 5 then 14 else 6) else (if j.val < 7 then 20 else 29))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 12 else 18) else (if j.val < 11 then 2 else 5)) else (if j.val < 14 then (if j.val < 13 then 10 else 1) else (if j.val < 15 then 3 else 11)))))
    (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

theorem beta_kernel : betaCertificate.hom.ker.map
    (Subgroup.closure (Set.range betaGenerators)).subtype =
      Subgroup.closure (Set.range coverKernelGenerators) :=
  betaCertificate.kernel_image_eq_of_rows coverKernelCertificate
    (fun i => (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 0) else (if i.val < 7 then 0 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 0) else (if i.val < 11 then 0 else 0)) else (if i.val < 14 then (if i.val < 13 then 0 else 0) else (if i.val < 15 then 0 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 0) else (if i.val < 19 then 0 else 0)) else (if i.val < 22 then (if i.val < 21 then 0 else 0) else (if i.val < 23 then 0 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 0) else (if i.val < 27 then 0 else 0)) else (if i.val < 30 then (if i.val < 29 then 0 else 0) else (if i.val < 31 then 0 else 1))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 0 else 0) else (if i.val < 35 then 2 else 0)) else (if i.val < 38 then (if i.val < 37 then 0 else 0) else (if i.val < 39 then 0 else 0))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 0 else 0) else (if i.val < 43 then 0 else 0)) else (if i.val < 46 then (if i.val < 45 then 0 else 0) else (if i.val < 47 then 0 else 0)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 0 else 0) else (if i.val < 51 then 0 else 0)) else (if i.val < 54 then (if i.val < 53 then 0 else 0) else (if i.val < 55 then 0 else 0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 0 else 0) else (if i.val < 59 then 3 else 0)) else (if i.val < 62 then (if i.val < 61 then 0 else 0) else (if i.val < 63 then 0 else 0)))))))
    (fun j => (if j.val < 2 then (if j.val < 1 then 0 else 31) else (if j.val < 3 then 34 else 58)))
    (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

end SymmetricSubgroupAsymptotics.BinaryChart8T16
