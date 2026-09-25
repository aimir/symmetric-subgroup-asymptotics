import SymmetricSubgroupAsymptotics.FiniteGroupCertificates

/-!
# Literal transport chart 16T1086

The permutation rows are the original rows from the committed binary menu,
converted to zero-based Lean notation. Cayley rows and words are untrusted
candidate witnesses; every certificate equation is checked by Lean's kernel.
No catalogue identification or external PASS output is used in a proof.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

private def alphaSourceLiteral0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral4 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral5 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral6 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral7 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral8 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral9 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral10 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral11 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral12 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral13 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral14 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral15 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral16 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral17 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral18 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral19 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral20 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral21 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral22 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral23 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral24 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral25 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral26 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral27 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral28 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral29 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral30 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral31 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral32 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral33 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral34 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral35 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral36 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral37 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral38 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral39 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral40 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral41 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral42 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,15,14,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral43 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral44 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,9,8,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral45 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,10,11,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,8,9,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral46 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral47 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral48 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,12,13,10,11,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral49 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral50 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral51 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral52 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral53 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral54 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral55 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral56 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral57 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral58 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral59 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral60 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral61 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral62 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral63 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral64 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral65 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral66 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral67 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral68 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral69 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral70 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral71 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral72 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral73 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral74 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral75 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,8,9,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral76 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral77 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral78 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,12,13,10,11,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral79 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral80 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral81 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral82 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral83 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral84 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral85 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral86 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral87 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral88 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral89 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral90 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral91 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral92 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,15,14,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral93 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral94 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,9,8,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral95 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,10,11,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,8,9,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral96 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral97 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral98 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral99 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral100 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral101 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral102 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral103 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral104 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral105 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral106 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral107 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral108 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral109 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral110 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral111 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral112 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,8,9,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral113 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral114 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,15,14,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral115 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral116 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,9,8,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral117 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,10,11,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral118 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral119 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral120 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,15,14,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral121 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral122 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral123 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral124 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,9,8,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral125 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,10,11,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral126 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral127 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,8,9,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral128 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral129 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,10,11,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral130 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,8,9,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral131 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral132 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral133 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,12,13,10,11,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral134 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral135 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral136 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,12,13,10,11,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral137 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral138 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral139 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral140 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral141 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral142 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral143 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral144 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral145 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral146 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral147 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral148 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral149 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,15,14,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral150 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral151 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral152 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral153 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral154 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral155 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral156 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral157 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral158 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral159 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral160 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral161 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral162 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral163 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral164 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral165 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral166 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral167 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral168 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,8,9,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral169 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral170 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral171 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral172 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral173 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral174 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral175 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral176 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral177 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral178 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral179 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral180 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral181 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral182 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral183 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral184 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral185 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,8,9,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral186 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral187 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral188 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral189 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral190 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral191 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral192 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral193 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral194 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral195 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral196 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral197 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral198 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral199 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral200 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,8,9,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral201 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral202 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral203 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,8,9,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral204 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral205 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral206 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,12,13,10,11,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral207 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral208 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral209 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,12,13,10,11,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral210 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral211 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral212 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral213 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral214 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral215 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral216 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral217 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral218 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral219 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral220 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral221 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral222 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral223 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral224 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral225 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral226 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral227 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral228 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral229 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral230 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral231 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral232 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral233 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral234 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral235 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral236 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral237 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,8,9,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral238 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral239 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,15,14,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral240 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral241 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,9,8,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral242 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,10,11,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral243 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral244 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,15,14,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral245 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral246 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral247 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,9,8,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral248 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,10,11,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral249 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral250 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,8,9,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral251 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral252 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,10,11,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral253 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,8,9,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral254 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral255 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral256 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral257 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral258 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral259 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral260 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral261 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral262 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral263 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral264 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral265 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral266 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral267 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral268 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral269 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral270 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral271 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral272 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,15,14,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral273 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral274 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral275 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral276 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral277 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral278 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral279 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral280 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral281 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral282 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral283 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral284 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral285 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral286 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral287 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral288 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral289 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral290 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral291 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral292 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral293 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral294 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral295 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral296 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,9,8,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral297 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral298 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral299 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral300 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral301 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral302 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral303 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral304 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral305 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral306 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral307 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral308 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral309 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral310 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral311 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,12,13,10,11,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral312 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral313 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral314 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral315 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral316 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral317 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral318 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral319 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral320 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral321 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral322 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral323 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral324 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral325 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral326 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral327 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral328 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral329 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral330 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral331 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral332 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral333 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral334 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral335 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral336 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral337 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,8,9,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral338 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral339 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral340 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral341 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral342 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral343 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral344 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral345 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral346 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral347 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral348 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral349 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral350 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral351 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral352 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral353 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral354 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral355 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral356 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral357 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral358 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral359 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral360 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral361 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral362 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral363 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral364 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral365 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral366 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral367 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral368 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral369 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral370 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral371 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral372 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral373 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral374 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,8,9,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral375 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral376 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral377 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral378 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral379 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral380 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral381 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral382 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral383 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral384 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral385 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral386 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral387 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,8,9,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral388 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral389 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral390 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,8,9,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral391 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral392 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral393 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral394 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral395 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral396 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral397 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral398 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral399 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral400 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral401 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral402 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral403 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral404 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral405 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral406 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral407 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral408 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral409 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral410 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral411 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral412 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral413 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral414 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral415 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral416 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral417 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral418 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral419 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral420 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral421 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral422 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral423 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral424 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral425 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral426 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral427 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral428 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral429 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral430 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral431 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral432 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral433 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral434 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral435 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral436 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral437 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral438 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral439 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral440 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral441 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral442 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral443 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral444 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral445 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral446 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral447 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral448 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,12,13,10,11,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral449 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral450 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral451 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral452 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral453 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral454 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral455 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral456 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral457 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral458 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral459 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,10,11,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral460 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral461 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral462 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral463 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral464 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral465 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral466 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral467 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral468 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral469 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral470 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral471 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral472 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral473 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral474 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,8,9,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral475 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral476 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral477 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral478 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral479 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral480 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral481 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral482 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral483 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral484 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral485 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral486 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral487 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral488 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral489 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral490 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral491 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral492 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral493 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral494 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral495 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,15,14,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral496 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral497 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral498 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral499 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,9,8,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral500 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral501 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral502 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral503 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral504 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral505 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral506 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral507 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral508 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral509 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral510 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral511 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral512 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral513 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral514 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral515 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral516 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,9,8,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral517 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral518 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral519 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral520 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral521 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral522 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral523 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral524 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral525 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral526 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral527 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral528 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral529 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral530 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral531 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral532 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral533 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral534 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral535 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral536 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral537 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral538 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral539 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral540 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral541 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral542 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral543 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral544 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral545 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral546 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral547 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral548 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral549 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,8,9,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral550 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral551 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral552 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral553 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral554 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral555 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral556 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral557 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral558 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral559 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral560 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral561 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral562 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral563 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral564 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral565 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral566 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral567 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral568 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral569 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral570 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,12,13,10,11,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral571 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral572 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral573 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral574 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral575 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral576 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral577 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral578 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral579 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral580 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral581 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral582 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral583 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,9,8,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral584 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral585 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral586 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,12,13,10,11,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral587 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral588 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral589 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral590 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral591 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral592 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral593 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral594 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral595 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral596 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral597 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral598 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral599 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral600 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral601 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral602 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral603 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral604 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral605 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral606 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral607 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral608 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral609 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral610 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral611 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral612 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,8,9,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral613 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral614 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral615 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral616 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,8,9,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral617 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral618 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral619 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,8,9,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral620 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral621 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral622 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral623 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral624 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral625 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral626 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral627 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral628 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral629 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral630 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral631 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral632 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral633 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral634 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral635 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral636 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral637 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral638 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral639 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral640 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral641 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral642 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral643 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral644 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral645 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral646 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral647 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral648 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral649 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral650 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral651 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral652 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral653 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral654 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral655 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral656 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral657 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral658 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral659 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral660 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral661 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral662 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral663 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral664 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral665 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral666 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral667 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral668 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral669 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral670 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,10,11,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral671 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral672 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral673 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral674 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral675 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral676 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral677 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral678 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral679 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral680 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral681 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral682 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral683 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral684 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral685 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,8,9,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral686 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral687 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral688 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral689 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral690 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral691 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral692 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral693 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral694 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral695 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral696 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral697 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral698 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral699 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral700 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral701 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral702 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral703 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral704 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,15,14,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral705 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral706 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,9,8,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,12,13,10,11,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral707 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral708 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral709 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral710 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral711 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral712 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral713 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral714 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral715 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral716 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral717 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral718 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral719 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral720 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral721 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,10,11,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral722 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,12,13,10,11,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral723 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral724 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral725 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral726 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral727 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral728 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral729 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral730 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral731 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral732 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,10,11,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral733 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral734 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral735 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral736 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral737 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral738 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral739 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,10,11,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral740 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral741 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral742 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral743 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral744 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral745 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral746 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral747 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral748 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,8,9,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral749 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral750 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral751 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral752 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,15,14,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,8,9,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral753 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,9,8,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral754 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral755 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,8,9,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral756 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral757 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral758 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral759 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral760 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral761 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral762 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral763 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral764 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,15,14,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral765 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,9,8,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral766 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral767 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,15,14,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral768 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral769 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral770 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,9,8,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral771 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral772 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral773 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral774 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral775 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral776 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral777 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral778 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral779 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral780 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral781 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral782 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral783 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral784 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral785 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral786 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral787 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral788 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral789 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral790 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral791 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral792 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral793 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral794 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral795 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral796 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral797 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral798 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral799 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral800 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral801 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral802 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral803 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral804 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,8,9,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral805 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral806 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral807 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,8,9,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral808 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral809 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral810 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,8,9,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral811 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral812 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral813 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral814 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral815 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,12,13,10,11,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral816 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral817 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral818 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral819 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral820 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral821 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral822 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral823 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,12,13,10,11,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral824 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral825 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral826 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral827 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral828 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral829 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral830 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral831 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral832 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral833 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral834 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral835 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral836 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral837 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral838 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral839 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral840 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral841 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral842 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral843 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral844 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral845 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral846 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral847 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral848 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral849 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral850 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral851 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral852 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral853 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral854 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral855 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral856 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral857 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral858 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral859 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral860 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral861 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral862 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral863 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral864 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral865 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral866 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral867 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral868 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral869 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,10,11,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral870 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral871 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral872 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral873 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral874 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,10,11,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral875 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral876 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral877 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral878 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral879 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral880 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral881 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,10,11,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral882 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral883 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral884 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral885 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral886 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral887 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral888 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral889 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral890 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,8,9,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral891 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral892 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral893 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,15,14,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,8,9,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral894 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,9,8,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral895 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral896 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,8,9,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral897 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral898 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral899 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral900 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral901 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,12,13,10,11,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral902 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral903 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral904 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral905 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,15,14,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral906 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,9,8,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral907 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral908 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,15,14,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral909 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,12,13,10,11,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral910 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral911 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral912 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral913 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral914 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral915 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral916 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral917 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral918 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral919 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral920 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral921 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral922 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral923 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral924 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral925 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral926 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral927 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral928 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral929 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral930 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral931 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral932 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral933 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral934 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral935 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral936 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral937 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral938 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral939 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral940 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral941 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral942 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral943 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral944 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral945 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral946 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral947 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral948 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral949 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral950 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral951 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral952 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral953 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral954 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral955 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral956 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral957 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral958 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral959 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral960 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral961 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral962 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral963 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral964 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral965 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral966 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral967 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral968 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral969 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral970 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral971 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral972 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral973 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral974 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral975 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral976 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral977 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral978 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral979 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral980 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral981 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral982 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral983 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral984 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral985 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral986 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral987 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral988 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral989 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral990 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral991 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral992 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral993 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral994 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral995 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral996 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral997 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral998 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral999 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1000 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1001 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1002 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1003 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1004 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1005 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1006 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1007 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1008 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1009 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1010 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1011 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1012 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1013 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1014 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1015 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1016 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1017 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1018 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1019 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1020 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1021 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1022 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSourceLiteral1023 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaSource (i : Fin 1024) : Equiv.Perm (Fin 16) :=
  (if i.val < 512 then (if i.val < 256 then (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then alphaSourceLiteral0 else alphaSourceLiteral1) else (if i.val < 3 then alphaSourceLiteral2 else alphaSourceLiteral3)) else (if i.val < 6 then (if i.val < 5 then alphaSourceLiteral4 else alphaSourceLiteral5) else (if i.val < 7 then alphaSourceLiteral6 else alphaSourceLiteral7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then alphaSourceLiteral8 else alphaSourceLiteral9) else (if i.val < 11 then alphaSourceLiteral10 else alphaSourceLiteral11)) else (if i.val < 14 then (if i.val < 13 then alphaSourceLiteral12 else alphaSourceLiteral13) else (if i.val < 15 then alphaSourceLiteral14 else alphaSourceLiteral15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then alphaSourceLiteral16 else alphaSourceLiteral17) else (if i.val < 19 then alphaSourceLiteral18 else alphaSourceLiteral19)) else (if i.val < 22 then (if i.val < 21 then alphaSourceLiteral20 else alphaSourceLiteral21) else (if i.val < 23 then alphaSourceLiteral22 else alphaSourceLiteral23))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then alphaSourceLiteral24 else alphaSourceLiteral25) else (if i.val < 27 then alphaSourceLiteral26 else alphaSourceLiteral27)) else (if i.val < 30 then (if i.val < 29 then alphaSourceLiteral28 else alphaSourceLiteral29) else (if i.val < 31 then alphaSourceLiteral30 else alphaSourceLiteral31))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then alphaSourceLiteral32 else alphaSourceLiteral33) else (if i.val < 35 then alphaSourceLiteral34 else alphaSourceLiteral35)) else (if i.val < 38 then (if i.val < 37 then alphaSourceLiteral36 else alphaSourceLiteral37) else (if i.val < 39 then alphaSourceLiteral38 else alphaSourceLiteral39))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then alphaSourceLiteral40 else alphaSourceLiteral41) else (if i.val < 43 then alphaSourceLiteral42 else alphaSourceLiteral43)) else (if i.val < 46 then (if i.val < 45 then alphaSourceLiteral44 else alphaSourceLiteral45) else (if i.val < 47 then alphaSourceLiteral46 else alphaSourceLiteral47)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then alphaSourceLiteral48 else alphaSourceLiteral49) else (if i.val < 51 then alphaSourceLiteral50 else alphaSourceLiteral51)) else (if i.val < 54 then (if i.val < 53 then alphaSourceLiteral52 else alphaSourceLiteral53) else (if i.val < 55 then alphaSourceLiteral54 else alphaSourceLiteral55))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then alphaSourceLiteral56 else alphaSourceLiteral57) else (if i.val < 59 then alphaSourceLiteral58 else alphaSourceLiteral59)) else (if i.val < 62 then (if i.val < 61 then alphaSourceLiteral60 else alphaSourceLiteral61) else (if i.val < 63 then alphaSourceLiteral62 else alphaSourceLiteral63)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then alphaSourceLiteral64 else alphaSourceLiteral65) else (if i.val < 67 then alphaSourceLiteral66 else alphaSourceLiteral67)) else (if i.val < 70 then (if i.val < 69 then alphaSourceLiteral68 else alphaSourceLiteral69) else (if i.val < 71 then alphaSourceLiteral70 else alphaSourceLiteral71))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then alphaSourceLiteral72 else alphaSourceLiteral73) else (if i.val < 75 then alphaSourceLiteral74 else alphaSourceLiteral75)) else (if i.val < 78 then (if i.val < 77 then alphaSourceLiteral76 else alphaSourceLiteral77) else (if i.val < 79 then alphaSourceLiteral78 else alphaSourceLiteral79)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then alphaSourceLiteral80 else alphaSourceLiteral81) else (if i.val < 83 then alphaSourceLiteral82 else alphaSourceLiteral83)) else (if i.val < 86 then (if i.val < 85 then alphaSourceLiteral84 else alphaSourceLiteral85) else (if i.val < 87 then alphaSourceLiteral86 else alphaSourceLiteral87))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then alphaSourceLiteral88 else alphaSourceLiteral89) else (if i.val < 91 then alphaSourceLiteral90 else alphaSourceLiteral91)) else (if i.val < 94 then (if i.val < 93 then alphaSourceLiteral92 else alphaSourceLiteral93) else (if i.val < 95 then alphaSourceLiteral94 else alphaSourceLiteral95))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then alphaSourceLiteral96 else alphaSourceLiteral97) else (if i.val < 99 then alphaSourceLiteral98 else alphaSourceLiteral99)) else (if i.val < 102 then (if i.val < 101 then alphaSourceLiteral100 else alphaSourceLiteral101) else (if i.val < 103 then alphaSourceLiteral102 else alphaSourceLiteral103))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then alphaSourceLiteral104 else alphaSourceLiteral105) else (if i.val < 107 then alphaSourceLiteral106 else alphaSourceLiteral107)) else (if i.val < 110 then (if i.val < 109 then alphaSourceLiteral108 else alphaSourceLiteral109) else (if i.val < 111 then alphaSourceLiteral110 else alphaSourceLiteral111)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then alphaSourceLiteral112 else alphaSourceLiteral113) else (if i.val < 115 then alphaSourceLiteral114 else alphaSourceLiteral115)) else (if i.val < 118 then (if i.val < 117 then alphaSourceLiteral116 else alphaSourceLiteral117) else (if i.val < 119 then alphaSourceLiteral118 else alphaSourceLiteral119))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then alphaSourceLiteral120 else alphaSourceLiteral121) else (if i.val < 123 then alphaSourceLiteral122 else alphaSourceLiteral123)) else (if i.val < 126 then (if i.val < 125 then alphaSourceLiteral124 else alphaSourceLiteral125) else (if i.val < 127 then alphaSourceLiteral126 else alphaSourceLiteral127))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then alphaSourceLiteral128 else alphaSourceLiteral129) else (if i.val < 131 then alphaSourceLiteral130 else alphaSourceLiteral131)) else (if i.val < 134 then (if i.val < 133 then alphaSourceLiteral132 else alphaSourceLiteral133) else (if i.val < 135 then alphaSourceLiteral134 else alphaSourceLiteral135))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then alphaSourceLiteral136 else alphaSourceLiteral137) else (if i.val < 139 then alphaSourceLiteral138 else alphaSourceLiteral139)) else (if i.val < 142 then (if i.val < 141 then alphaSourceLiteral140 else alphaSourceLiteral141) else (if i.val < 143 then alphaSourceLiteral142 else alphaSourceLiteral143)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then alphaSourceLiteral144 else alphaSourceLiteral145) else (if i.val < 147 then alphaSourceLiteral146 else alphaSourceLiteral147)) else (if i.val < 150 then (if i.val < 149 then alphaSourceLiteral148 else alphaSourceLiteral149) else (if i.val < 151 then alphaSourceLiteral150 else alphaSourceLiteral151))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then alphaSourceLiteral152 else alphaSourceLiteral153) else (if i.val < 155 then alphaSourceLiteral154 else alphaSourceLiteral155)) else (if i.val < 158 then (if i.val < 157 then alphaSourceLiteral156 else alphaSourceLiteral157) else (if i.val < 159 then alphaSourceLiteral158 else alphaSourceLiteral159))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then alphaSourceLiteral160 else alphaSourceLiteral161) else (if i.val < 163 then alphaSourceLiteral162 else alphaSourceLiteral163)) else (if i.val < 166 then (if i.val < 165 then alphaSourceLiteral164 else alphaSourceLiteral165) else (if i.val < 167 then alphaSourceLiteral166 else alphaSourceLiteral167))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then alphaSourceLiteral168 else alphaSourceLiteral169) else (if i.val < 171 then alphaSourceLiteral170 else alphaSourceLiteral171)) else (if i.val < 174 then (if i.val < 173 then alphaSourceLiteral172 else alphaSourceLiteral173) else (if i.val < 175 then alphaSourceLiteral174 else alphaSourceLiteral175)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then alphaSourceLiteral176 else alphaSourceLiteral177) else (if i.val < 179 then alphaSourceLiteral178 else alphaSourceLiteral179)) else (if i.val < 182 then (if i.val < 181 then alphaSourceLiteral180 else alphaSourceLiteral181) else (if i.val < 183 then alphaSourceLiteral182 else alphaSourceLiteral183))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then alphaSourceLiteral184 else alphaSourceLiteral185) else (if i.val < 187 then alphaSourceLiteral186 else alphaSourceLiteral187)) else (if i.val < 190 then (if i.val < 189 then alphaSourceLiteral188 else alphaSourceLiteral189) else (if i.val < 191 then alphaSourceLiteral190 else alphaSourceLiteral191)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then alphaSourceLiteral192 else alphaSourceLiteral193) else (if i.val < 195 then alphaSourceLiteral194 else alphaSourceLiteral195)) else (if i.val < 198 then (if i.val < 197 then alphaSourceLiteral196 else alphaSourceLiteral197) else (if i.val < 199 then alphaSourceLiteral198 else alphaSourceLiteral199))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then alphaSourceLiteral200 else alphaSourceLiteral201) else (if i.val < 203 then alphaSourceLiteral202 else alphaSourceLiteral203)) else (if i.val < 206 then (if i.val < 205 then alphaSourceLiteral204 else alphaSourceLiteral205) else (if i.val < 207 then alphaSourceLiteral206 else alphaSourceLiteral207)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then alphaSourceLiteral208 else alphaSourceLiteral209) else (if i.val < 211 then alphaSourceLiteral210 else alphaSourceLiteral211)) else (if i.val < 214 then (if i.val < 213 then alphaSourceLiteral212 else alphaSourceLiteral213) else (if i.val < 215 then alphaSourceLiteral214 else alphaSourceLiteral215))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then alphaSourceLiteral216 else alphaSourceLiteral217) else (if i.val < 219 then alphaSourceLiteral218 else alphaSourceLiteral219)) else (if i.val < 222 then (if i.val < 221 then alphaSourceLiteral220 else alphaSourceLiteral221) else (if i.val < 223 then alphaSourceLiteral222 else alphaSourceLiteral223))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then alphaSourceLiteral224 else alphaSourceLiteral225) else (if i.val < 227 then alphaSourceLiteral226 else alphaSourceLiteral227)) else (if i.val < 230 then (if i.val < 229 then alphaSourceLiteral228 else alphaSourceLiteral229) else (if i.val < 231 then alphaSourceLiteral230 else alphaSourceLiteral231))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then alphaSourceLiteral232 else alphaSourceLiteral233) else (if i.val < 235 then alphaSourceLiteral234 else alphaSourceLiteral235)) else (if i.val < 238 then (if i.val < 237 then alphaSourceLiteral236 else alphaSourceLiteral237) else (if i.val < 239 then alphaSourceLiteral238 else alphaSourceLiteral239)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then alphaSourceLiteral240 else alphaSourceLiteral241) else (if i.val < 243 then alphaSourceLiteral242 else alphaSourceLiteral243)) else (if i.val < 246 then (if i.val < 245 then alphaSourceLiteral244 else alphaSourceLiteral245) else (if i.val < 247 then alphaSourceLiteral246 else alphaSourceLiteral247))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then alphaSourceLiteral248 else alphaSourceLiteral249) else (if i.val < 251 then alphaSourceLiteral250 else alphaSourceLiteral251)) else (if i.val < 254 then (if i.val < 253 then alphaSourceLiteral252 else alphaSourceLiteral253) else (if i.val < 255 then alphaSourceLiteral254 else alphaSourceLiteral255)))))))) else (if i.val < 384 then (if i.val < 320 then (if i.val < 288 then (if i.val < 272 then (if i.val < 264 then (if i.val < 260 then (if i.val < 258 then (if i.val < 257 then alphaSourceLiteral256 else alphaSourceLiteral257) else (if i.val < 259 then alphaSourceLiteral258 else alphaSourceLiteral259)) else (if i.val < 262 then (if i.val < 261 then alphaSourceLiteral260 else alphaSourceLiteral261) else (if i.val < 263 then alphaSourceLiteral262 else alphaSourceLiteral263))) else (if i.val < 268 then (if i.val < 266 then (if i.val < 265 then alphaSourceLiteral264 else alphaSourceLiteral265) else (if i.val < 267 then alphaSourceLiteral266 else alphaSourceLiteral267)) else (if i.val < 270 then (if i.val < 269 then alphaSourceLiteral268 else alphaSourceLiteral269) else (if i.val < 271 then alphaSourceLiteral270 else alphaSourceLiteral271)))) else (if i.val < 280 then (if i.val < 276 then (if i.val < 274 then (if i.val < 273 then alphaSourceLiteral272 else alphaSourceLiteral273) else (if i.val < 275 then alphaSourceLiteral274 else alphaSourceLiteral275)) else (if i.val < 278 then (if i.val < 277 then alphaSourceLiteral276 else alphaSourceLiteral277) else (if i.val < 279 then alphaSourceLiteral278 else alphaSourceLiteral279))) else (if i.val < 284 then (if i.val < 282 then (if i.val < 281 then alphaSourceLiteral280 else alphaSourceLiteral281) else (if i.val < 283 then alphaSourceLiteral282 else alphaSourceLiteral283)) else (if i.val < 286 then (if i.val < 285 then alphaSourceLiteral284 else alphaSourceLiteral285) else (if i.val < 287 then alphaSourceLiteral286 else alphaSourceLiteral287))))) else (if i.val < 304 then (if i.val < 296 then (if i.val < 292 then (if i.val < 290 then (if i.val < 289 then alphaSourceLiteral288 else alphaSourceLiteral289) else (if i.val < 291 then alphaSourceLiteral290 else alphaSourceLiteral291)) else (if i.val < 294 then (if i.val < 293 then alphaSourceLiteral292 else alphaSourceLiteral293) else (if i.val < 295 then alphaSourceLiteral294 else alphaSourceLiteral295))) else (if i.val < 300 then (if i.val < 298 then (if i.val < 297 then alphaSourceLiteral296 else alphaSourceLiteral297) else (if i.val < 299 then alphaSourceLiteral298 else alphaSourceLiteral299)) else (if i.val < 302 then (if i.val < 301 then alphaSourceLiteral300 else alphaSourceLiteral301) else (if i.val < 303 then alphaSourceLiteral302 else alphaSourceLiteral303)))) else (if i.val < 312 then (if i.val < 308 then (if i.val < 306 then (if i.val < 305 then alphaSourceLiteral304 else alphaSourceLiteral305) else (if i.val < 307 then alphaSourceLiteral306 else alphaSourceLiteral307)) else (if i.val < 310 then (if i.val < 309 then alphaSourceLiteral308 else alphaSourceLiteral309) else (if i.val < 311 then alphaSourceLiteral310 else alphaSourceLiteral311))) else (if i.val < 316 then (if i.val < 314 then (if i.val < 313 then alphaSourceLiteral312 else alphaSourceLiteral313) else (if i.val < 315 then alphaSourceLiteral314 else alphaSourceLiteral315)) else (if i.val < 318 then (if i.val < 317 then alphaSourceLiteral316 else alphaSourceLiteral317) else (if i.val < 319 then alphaSourceLiteral318 else alphaSourceLiteral319)))))) else (if i.val < 352 then (if i.val < 336 then (if i.val < 328 then (if i.val < 324 then (if i.val < 322 then (if i.val < 321 then alphaSourceLiteral320 else alphaSourceLiteral321) else (if i.val < 323 then alphaSourceLiteral322 else alphaSourceLiteral323)) else (if i.val < 326 then (if i.val < 325 then alphaSourceLiteral324 else alphaSourceLiteral325) else (if i.val < 327 then alphaSourceLiteral326 else alphaSourceLiteral327))) else (if i.val < 332 then (if i.val < 330 then (if i.val < 329 then alphaSourceLiteral328 else alphaSourceLiteral329) else (if i.val < 331 then alphaSourceLiteral330 else alphaSourceLiteral331)) else (if i.val < 334 then (if i.val < 333 then alphaSourceLiteral332 else alphaSourceLiteral333) else (if i.val < 335 then alphaSourceLiteral334 else alphaSourceLiteral335)))) else (if i.val < 344 then (if i.val < 340 then (if i.val < 338 then (if i.val < 337 then alphaSourceLiteral336 else alphaSourceLiteral337) else (if i.val < 339 then alphaSourceLiteral338 else alphaSourceLiteral339)) else (if i.val < 342 then (if i.val < 341 then alphaSourceLiteral340 else alphaSourceLiteral341) else (if i.val < 343 then alphaSourceLiteral342 else alphaSourceLiteral343))) else (if i.val < 348 then (if i.val < 346 then (if i.val < 345 then alphaSourceLiteral344 else alphaSourceLiteral345) else (if i.val < 347 then alphaSourceLiteral346 else alphaSourceLiteral347)) else (if i.val < 350 then (if i.val < 349 then alphaSourceLiteral348 else alphaSourceLiteral349) else (if i.val < 351 then alphaSourceLiteral350 else alphaSourceLiteral351))))) else (if i.val < 368 then (if i.val < 360 then (if i.val < 356 then (if i.val < 354 then (if i.val < 353 then alphaSourceLiteral352 else alphaSourceLiteral353) else (if i.val < 355 then alphaSourceLiteral354 else alphaSourceLiteral355)) else (if i.val < 358 then (if i.val < 357 then alphaSourceLiteral356 else alphaSourceLiteral357) else (if i.val < 359 then alphaSourceLiteral358 else alphaSourceLiteral359))) else (if i.val < 364 then (if i.val < 362 then (if i.val < 361 then alphaSourceLiteral360 else alphaSourceLiteral361) else (if i.val < 363 then alphaSourceLiteral362 else alphaSourceLiteral363)) else (if i.val < 366 then (if i.val < 365 then alphaSourceLiteral364 else alphaSourceLiteral365) else (if i.val < 367 then alphaSourceLiteral366 else alphaSourceLiteral367)))) else (if i.val < 376 then (if i.val < 372 then (if i.val < 370 then (if i.val < 369 then alphaSourceLiteral368 else alphaSourceLiteral369) else (if i.val < 371 then alphaSourceLiteral370 else alphaSourceLiteral371)) else (if i.val < 374 then (if i.val < 373 then alphaSourceLiteral372 else alphaSourceLiteral373) else (if i.val < 375 then alphaSourceLiteral374 else alphaSourceLiteral375))) else (if i.val < 380 then (if i.val < 378 then (if i.val < 377 then alphaSourceLiteral376 else alphaSourceLiteral377) else (if i.val < 379 then alphaSourceLiteral378 else alphaSourceLiteral379)) else (if i.val < 382 then (if i.val < 381 then alphaSourceLiteral380 else alphaSourceLiteral381) else (if i.val < 383 then alphaSourceLiteral382 else alphaSourceLiteral383))))))) else (if i.val < 448 then (if i.val < 416 then (if i.val < 400 then (if i.val < 392 then (if i.val < 388 then (if i.val < 386 then (if i.val < 385 then alphaSourceLiteral384 else alphaSourceLiteral385) else (if i.val < 387 then alphaSourceLiteral386 else alphaSourceLiteral387)) else (if i.val < 390 then (if i.val < 389 then alphaSourceLiteral388 else alphaSourceLiteral389) else (if i.val < 391 then alphaSourceLiteral390 else alphaSourceLiteral391))) else (if i.val < 396 then (if i.val < 394 then (if i.val < 393 then alphaSourceLiteral392 else alphaSourceLiteral393) else (if i.val < 395 then alphaSourceLiteral394 else alphaSourceLiteral395)) else (if i.val < 398 then (if i.val < 397 then alphaSourceLiteral396 else alphaSourceLiteral397) else (if i.val < 399 then alphaSourceLiteral398 else alphaSourceLiteral399)))) else (if i.val < 408 then (if i.val < 404 then (if i.val < 402 then (if i.val < 401 then alphaSourceLiteral400 else alphaSourceLiteral401) else (if i.val < 403 then alphaSourceLiteral402 else alphaSourceLiteral403)) else (if i.val < 406 then (if i.val < 405 then alphaSourceLiteral404 else alphaSourceLiteral405) else (if i.val < 407 then alphaSourceLiteral406 else alphaSourceLiteral407))) else (if i.val < 412 then (if i.val < 410 then (if i.val < 409 then alphaSourceLiteral408 else alphaSourceLiteral409) else (if i.val < 411 then alphaSourceLiteral410 else alphaSourceLiteral411)) else (if i.val < 414 then (if i.val < 413 then alphaSourceLiteral412 else alphaSourceLiteral413) else (if i.val < 415 then alphaSourceLiteral414 else alphaSourceLiteral415))))) else (if i.val < 432 then (if i.val < 424 then (if i.val < 420 then (if i.val < 418 then (if i.val < 417 then alphaSourceLiteral416 else alphaSourceLiteral417) else (if i.val < 419 then alphaSourceLiteral418 else alphaSourceLiteral419)) else (if i.val < 422 then (if i.val < 421 then alphaSourceLiteral420 else alphaSourceLiteral421) else (if i.val < 423 then alphaSourceLiteral422 else alphaSourceLiteral423))) else (if i.val < 428 then (if i.val < 426 then (if i.val < 425 then alphaSourceLiteral424 else alphaSourceLiteral425) else (if i.val < 427 then alphaSourceLiteral426 else alphaSourceLiteral427)) else (if i.val < 430 then (if i.val < 429 then alphaSourceLiteral428 else alphaSourceLiteral429) else (if i.val < 431 then alphaSourceLiteral430 else alphaSourceLiteral431)))) else (if i.val < 440 then (if i.val < 436 then (if i.val < 434 then (if i.val < 433 then alphaSourceLiteral432 else alphaSourceLiteral433) else (if i.val < 435 then alphaSourceLiteral434 else alphaSourceLiteral435)) else (if i.val < 438 then (if i.val < 437 then alphaSourceLiteral436 else alphaSourceLiteral437) else (if i.val < 439 then alphaSourceLiteral438 else alphaSourceLiteral439))) else (if i.val < 444 then (if i.val < 442 then (if i.val < 441 then alphaSourceLiteral440 else alphaSourceLiteral441) else (if i.val < 443 then alphaSourceLiteral442 else alphaSourceLiteral443)) else (if i.val < 446 then (if i.val < 445 then alphaSourceLiteral444 else alphaSourceLiteral445) else (if i.val < 447 then alphaSourceLiteral446 else alphaSourceLiteral447)))))) else (if i.val < 480 then (if i.val < 464 then (if i.val < 456 then (if i.val < 452 then (if i.val < 450 then (if i.val < 449 then alphaSourceLiteral448 else alphaSourceLiteral449) else (if i.val < 451 then alphaSourceLiteral450 else alphaSourceLiteral451)) else (if i.val < 454 then (if i.val < 453 then alphaSourceLiteral452 else alphaSourceLiteral453) else (if i.val < 455 then alphaSourceLiteral454 else alphaSourceLiteral455))) else (if i.val < 460 then (if i.val < 458 then (if i.val < 457 then alphaSourceLiteral456 else alphaSourceLiteral457) else (if i.val < 459 then alphaSourceLiteral458 else alphaSourceLiteral459)) else (if i.val < 462 then (if i.val < 461 then alphaSourceLiteral460 else alphaSourceLiteral461) else (if i.val < 463 then alphaSourceLiteral462 else alphaSourceLiteral463)))) else (if i.val < 472 then (if i.val < 468 then (if i.val < 466 then (if i.val < 465 then alphaSourceLiteral464 else alphaSourceLiteral465) else (if i.val < 467 then alphaSourceLiteral466 else alphaSourceLiteral467)) else (if i.val < 470 then (if i.val < 469 then alphaSourceLiteral468 else alphaSourceLiteral469) else (if i.val < 471 then alphaSourceLiteral470 else alphaSourceLiteral471))) else (if i.val < 476 then (if i.val < 474 then (if i.val < 473 then alphaSourceLiteral472 else alphaSourceLiteral473) else (if i.val < 475 then alphaSourceLiteral474 else alphaSourceLiteral475)) else (if i.val < 478 then (if i.val < 477 then alphaSourceLiteral476 else alphaSourceLiteral477) else (if i.val < 479 then alphaSourceLiteral478 else alphaSourceLiteral479))))) else (if i.val < 496 then (if i.val < 488 then (if i.val < 484 then (if i.val < 482 then (if i.val < 481 then alphaSourceLiteral480 else alphaSourceLiteral481) else (if i.val < 483 then alphaSourceLiteral482 else alphaSourceLiteral483)) else (if i.val < 486 then (if i.val < 485 then alphaSourceLiteral484 else alphaSourceLiteral485) else (if i.val < 487 then alphaSourceLiteral486 else alphaSourceLiteral487))) else (if i.val < 492 then (if i.val < 490 then (if i.val < 489 then alphaSourceLiteral488 else alphaSourceLiteral489) else (if i.val < 491 then alphaSourceLiteral490 else alphaSourceLiteral491)) else (if i.val < 494 then (if i.val < 493 then alphaSourceLiteral492 else alphaSourceLiteral493) else (if i.val < 495 then alphaSourceLiteral494 else alphaSourceLiteral495)))) else (if i.val < 504 then (if i.val < 500 then (if i.val < 498 then (if i.val < 497 then alphaSourceLiteral496 else alphaSourceLiteral497) else (if i.val < 499 then alphaSourceLiteral498 else alphaSourceLiteral499)) else (if i.val < 502 then (if i.val < 501 then alphaSourceLiteral500 else alphaSourceLiteral501) else (if i.val < 503 then alphaSourceLiteral502 else alphaSourceLiteral503))) else (if i.val < 508 then (if i.val < 506 then (if i.val < 505 then alphaSourceLiteral504 else alphaSourceLiteral505) else (if i.val < 507 then alphaSourceLiteral506 else alphaSourceLiteral507)) else (if i.val < 510 then (if i.val < 509 then alphaSourceLiteral508 else alphaSourceLiteral509) else (if i.val < 511 then alphaSourceLiteral510 else alphaSourceLiteral511))))))))) else (if i.val < 768 then (if i.val < 640 then (if i.val < 576 then (if i.val < 544 then (if i.val < 528 then (if i.val < 520 then (if i.val < 516 then (if i.val < 514 then (if i.val < 513 then alphaSourceLiteral512 else alphaSourceLiteral513) else (if i.val < 515 then alphaSourceLiteral514 else alphaSourceLiteral515)) else (if i.val < 518 then (if i.val < 517 then alphaSourceLiteral516 else alphaSourceLiteral517) else (if i.val < 519 then alphaSourceLiteral518 else alphaSourceLiteral519))) else (if i.val < 524 then (if i.val < 522 then (if i.val < 521 then alphaSourceLiteral520 else alphaSourceLiteral521) else (if i.val < 523 then alphaSourceLiteral522 else alphaSourceLiteral523)) else (if i.val < 526 then (if i.val < 525 then alphaSourceLiteral524 else alphaSourceLiteral525) else (if i.val < 527 then alphaSourceLiteral526 else alphaSourceLiteral527)))) else (if i.val < 536 then (if i.val < 532 then (if i.val < 530 then (if i.val < 529 then alphaSourceLiteral528 else alphaSourceLiteral529) else (if i.val < 531 then alphaSourceLiteral530 else alphaSourceLiteral531)) else (if i.val < 534 then (if i.val < 533 then alphaSourceLiteral532 else alphaSourceLiteral533) else (if i.val < 535 then alphaSourceLiteral534 else alphaSourceLiteral535))) else (if i.val < 540 then (if i.val < 538 then (if i.val < 537 then alphaSourceLiteral536 else alphaSourceLiteral537) else (if i.val < 539 then alphaSourceLiteral538 else alphaSourceLiteral539)) else (if i.val < 542 then (if i.val < 541 then alphaSourceLiteral540 else alphaSourceLiteral541) else (if i.val < 543 then alphaSourceLiteral542 else alphaSourceLiteral543))))) else (if i.val < 560 then (if i.val < 552 then (if i.val < 548 then (if i.val < 546 then (if i.val < 545 then alphaSourceLiteral544 else alphaSourceLiteral545) else (if i.val < 547 then alphaSourceLiteral546 else alphaSourceLiteral547)) else (if i.val < 550 then (if i.val < 549 then alphaSourceLiteral548 else alphaSourceLiteral549) else (if i.val < 551 then alphaSourceLiteral550 else alphaSourceLiteral551))) else (if i.val < 556 then (if i.val < 554 then (if i.val < 553 then alphaSourceLiteral552 else alphaSourceLiteral553) else (if i.val < 555 then alphaSourceLiteral554 else alphaSourceLiteral555)) else (if i.val < 558 then (if i.val < 557 then alphaSourceLiteral556 else alphaSourceLiteral557) else (if i.val < 559 then alphaSourceLiteral558 else alphaSourceLiteral559)))) else (if i.val < 568 then (if i.val < 564 then (if i.val < 562 then (if i.val < 561 then alphaSourceLiteral560 else alphaSourceLiteral561) else (if i.val < 563 then alphaSourceLiteral562 else alphaSourceLiteral563)) else (if i.val < 566 then (if i.val < 565 then alphaSourceLiteral564 else alphaSourceLiteral565) else (if i.val < 567 then alphaSourceLiteral566 else alphaSourceLiteral567))) else (if i.val < 572 then (if i.val < 570 then (if i.val < 569 then alphaSourceLiteral568 else alphaSourceLiteral569) else (if i.val < 571 then alphaSourceLiteral570 else alphaSourceLiteral571)) else (if i.val < 574 then (if i.val < 573 then alphaSourceLiteral572 else alphaSourceLiteral573) else (if i.val < 575 then alphaSourceLiteral574 else alphaSourceLiteral575)))))) else (if i.val < 608 then (if i.val < 592 then (if i.val < 584 then (if i.val < 580 then (if i.val < 578 then (if i.val < 577 then alphaSourceLiteral576 else alphaSourceLiteral577) else (if i.val < 579 then alphaSourceLiteral578 else alphaSourceLiteral579)) else (if i.val < 582 then (if i.val < 581 then alphaSourceLiteral580 else alphaSourceLiteral581) else (if i.val < 583 then alphaSourceLiteral582 else alphaSourceLiteral583))) else (if i.val < 588 then (if i.val < 586 then (if i.val < 585 then alphaSourceLiteral584 else alphaSourceLiteral585) else (if i.val < 587 then alphaSourceLiteral586 else alphaSourceLiteral587)) else (if i.val < 590 then (if i.val < 589 then alphaSourceLiteral588 else alphaSourceLiteral589) else (if i.val < 591 then alphaSourceLiteral590 else alphaSourceLiteral591)))) else (if i.val < 600 then (if i.val < 596 then (if i.val < 594 then (if i.val < 593 then alphaSourceLiteral592 else alphaSourceLiteral593) else (if i.val < 595 then alphaSourceLiteral594 else alphaSourceLiteral595)) else (if i.val < 598 then (if i.val < 597 then alphaSourceLiteral596 else alphaSourceLiteral597) else (if i.val < 599 then alphaSourceLiteral598 else alphaSourceLiteral599))) else (if i.val < 604 then (if i.val < 602 then (if i.val < 601 then alphaSourceLiteral600 else alphaSourceLiteral601) else (if i.val < 603 then alphaSourceLiteral602 else alphaSourceLiteral603)) else (if i.val < 606 then (if i.val < 605 then alphaSourceLiteral604 else alphaSourceLiteral605) else (if i.val < 607 then alphaSourceLiteral606 else alphaSourceLiteral607))))) else (if i.val < 624 then (if i.val < 616 then (if i.val < 612 then (if i.val < 610 then (if i.val < 609 then alphaSourceLiteral608 else alphaSourceLiteral609) else (if i.val < 611 then alphaSourceLiteral610 else alphaSourceLiteral611)) else (if i.val < 614 then (if i.val < 613 then alphaSourceLiteral612 else alphaSourceLiteral613) else (if i.val < 615 then alphaSourceLiteral614 else alphaSourceLiteral615))) else (if i.val < 620 then (if i.val < 618 then (if i.val < 617 then alphaSourceLiteral616 else alphaSourceLiteral617) else (if i.val < 619 then alphaSourceLiteral618 else alphaSourceLiteral619)) else (if i.val < 622 then (if i.val < 621 then alphaSourceLiteral620 else alphaSourceLiteral621) else (if i.val < 623 then alphaSourceLiteral622 else alphaSourceLiteral623)))) else (if i.val < 632 then (if i.val < 628 then (if i.val < 626 then (if i.val < 625 then alphaSourceLiteral624 else alphaSourceLiteral625) else (if i.val < 627 then alphaSourceLiteral626 else alphaSourceLiteral627)) else (if i.val < 630 then (if i.val < 629 then alphaSourceLiteral628 else alphaSourceLiteral629) else (if i.val < 631 then alphaSourceLiteral630 else alphaSourceLiteral631))) else (if i.val < 636 then (if i.val < 634 then (if i.val < 633 then alphaSourceLiteral632 else alphaSourceLiteral633) else (if i.val < 635 then alphaSourceLiteral634 else alphaSourceLiteral635)) else (if i.val < 638 then (if i.val < 637 then alphaSourceLiteral636 else alphaSourceLiteral637) else (if i.val < 639 then alphaSourceLiteral638 else alphaSourceLiteral639))))))) else (if i.val < 704 then (if i.val < 672 then (if i.val < 656 then (if i.val < 648 then (if i.val < 644 then (if i.val < 642 then (if i.val < 641 then alphaSourceLiteral640 else alphaSourceLiteral641) else (if i.val < 643 then alphaSourceLiteral642 else alphaSourceLiteral643)) else (if i.val < 646 then (if i.val < 645 then alphaSourceLiteral644 else alphaSourceLiteral645) else (if i.val < 647 then alphaSourceLiteral646 else alphaSourceLiteral647))) else (if i.val < 652 then (if i.val < 650 then (if i.val < 649 then alphaSourceLiteral648 else alphaSourceLiteral649) else (if i.val < 651 then alphaSourceLiteral650 else alphaSourceLiteral651)) else (if i.val < 654 then (if i.val < 653 then alphaSourceLiteral652 else alphaSourceLiteral653) else (if i.val < 655 then alphaSourceLiteral654 else alphaSourceLiteral655)))) else (if i.val < 664 then (if i.val < 660 then (if i.val < 658 then (if i.val < 657 then alphaSourceLiteral656 else alphaSourceLiteral657) else (if i.val < 659 then alphaSourceLiteral658 else alphaSourceLiteral659)) else (if i.val < 662 then (if i.val < 661 then alphaSourceLiteral660 else alphaSourceLiteral661) else (if i.val < 663 then alphaSourceLiteral662 else alphaSourceLiteral663))) else (if i.val < 668 then (if i.val < 666 then (if i.val < 665 then alphaSourceLiteral664 else alphaSourceLiteral665) else (if i.val < 667 then alphaSourceLiteral666 else alphaSourceLiteral667)) else (if i.val < 670 then (if i.val < 669 then alphaSourceLiteral668 else alphaSourceLiteral669) else (if i.val < 671 then alphaSourceLiteral670 else alphaSourceLiteral671))))) else (if i.val < 688 then (if i.val < 680 then (if i.val < 676 then (if i.val < 674 then (if i.val < 673 then alphaSourceLiteral672 else alphaSourceLiteral673) else (if i.val < 675 then alphaSourceLiteral674 else alphaSourceLiteral675)) else (if i.val < 678 then (if i.val < 677 then alphaSourceLiteral676 else alphaSourceLiteral677) else (if i.val < 679 then alphaSourceLiteral678 else alphaSourceLiteral679))) else (if i.val < 684 then (if i.val < 682 then (if i.val < 681 then alphaSourceLiteral680 else alphaSourceLiteral681) else (if i.val < 683 then alphaSourceLiteral682 else alphaSourceLiteral683)) else (if i.val < 686 then (if i.val < 685 then alphaSourceLiteral684 else alphaSourceLiteral685) else (if i.val < 687 then alphaSourceLiteral686 else alphaSourceLiteral687)))) else (if i.val < 696 then (if i.val < 692 then (if i.val < 690 then (if i.val < 689 then alphaSourceLiteral688 else alphaSourceLiteral689) else (if i.val < 691 then alphaSourceLiteral690 else alphaSourceLiteral691)) else (if i.val < 694 then (if i.val < 693 then alphaSourceLiteral692 else alphaSourceLiteral693) else (if i.val < 695 then alphaSourceLiteral694 else alphaSourceLiteral695))) else (if i.val < 700 then (if i.val < 698 then (if i.val < 697 then alphaSourceLiteral696 else alphaSourceLiteral697) else (if i.val < 699 then alphaSourceLiteral698 else alphaSourceLiteral699)) else (if i.val < 702 then (if i.val < 701 then alphaSourceLiteral700 else alphaSourceLiteral701) else (if i.val < 703 then alphaSourceLiteral702 else alphaSourceLiteral703)))))) else (if i.val < 736 then (if i.val < 720 then (if i.val < 712 then (if i.val < 708 then (if i.val < 706 then (if i.val < 705 then alphaSourceLiteral704 else alphaSourceLiteral705) else (if i.val < 707 then alphaSourceLiteral706 else alphaSourceLiteral707)) else (if i.val < 710 then (if i.val < 709 then alphaSourceLiteral708 else alphaSourceLiteral709) else (if i.val < 711 then alphaSourceLiteral710 else alphaSourceLiteral711))) else (if i.val < 716 then (if i.val < 714 then (if i.val < 713 then alphaSourceLiteral712 else alphaSourceLiteral713) else (if i.val < 715 then alphaSourceLiteral714 else alphaSourceLiteral715)) else (if i.val < 718 then (if i.val < 717 then alphaSourceLiteral716 else alphaSourceLiteral717) else (if i.val < 719 then alphaSourceLiteral718 else alphaSourceLiteral719)))) else (if i.val < 728 then (if i.val < 724 then (if i.val < 722 then (if i.val < 721 then alphaSourceLiteral720 else alphaSourceLiteral721) else (if i.val < 723 then alphaSourceLiteral722 else alphaSourceLiteral723)) else (if i.val < 726 then (if i.val < 725 then alphaSourceLiteral724 else alphaSourceLiteral725) else (if i.val < 727 then alphaSourceLiteral726 else alphaSourceLiteral727))) else (if i.val < 732 then (if i.val < 730 then (if i.val < 729 then alphaSourceLiteral728 else alphaSourceLiteral729) else (if i.val < 731 then alphaSourceLiteral730 else alphaSourceLiteral731)) else (if i.val < 734 then (if i.val < 733 then alphaSourceLiteral732 else alphaSourceLiteral733) else (if i.val < 735 then alphaSourceLiteral734 else alphaSourceLiteral735))))) else (if i.val < 752 then (if i.val < 744 then (if i.val < 740 then (if i.val < 738 then (if i.val < 737 then alphaSourceLiteral736 else alphaSourceLiteral737) else (if i.val < 739 then alphaSourceLiteral738 else alphaSourceLiteral739)) else (if i.val < 742 then (if i.val < 741 then alphaSourceLiteral740 else alphaSourceLiteral741) else (if i.val < 743 then alphaSourceLiteral742 else alphaSourceLiteral743))) else (if i.val < 748 then (if i.val < 746 then (if i.val < 745 then alphaSourceLiteral744 else alphaSourceLiteral745) else (if i.val < 747 then alphaSourceLiteral746 else alphaSourceLiteral747)) else (if i.val < 750 then (if i.val < 749 then alphaSourceLiteral748 else alphaSourceLiteral749) else (if i.val < 751 then alphaSourceLiteral750 else alphaSourceLiteral751)))) else (if i.val < 760 then (if i.val < 756 then (if i.val < 754 then (if i.val < 753 then alphaSourceLiteral752 else alphaSourceLiteral753) else (if i.val < 755 then alphaSourceLiteral754 else alphaSourceLiteral755)) else (if i.val < 758 then (if i.val < 757 then alphaSourceLiteral756 else alphaSourceLiteral757) else (if i.val < 759 then alphaSourceLiteral758 else alphaSourceLiteral759))) else (if i.val < 764 then (if i.val < 762 then (if i.val < 761 then alphaSourceLiteral760 else alphaSourceLiteral761) else (if i.val < 763 then alphaSourceLiteral762 else alphaSourceLiteral763)) else (if i.val < 766 then (if i.val < 765 then alphaSourceLiteral764 else alphaSourceLiteral765) else (if i.val < 767 then alphaSourceLiteral766 else alphaSourceLiteral767)))))))) else (if i.val < 896 then (if i.val < 832 then (if i.val < 800 then (if i.val < 784 then (if i.val < 776 then (if i.val < 772 then (if i.val < 770 then (if i.val < 769 then alphaSourceLiteral768 else alphaSourceLiteral769) else (if i.val < 771 then alphaSourceLiteral770 else alphaSourceLiteral771)) else (if i.val < 774 then (if i.val < 773 then alphaSourceLiteral772 else alphaSourceLiteral773) else (if i.val < 775 then alphaSourceLiteral774 else alphaSourceLiteral775))) else (if i.val < 780 then (if i.val < 778 then (if i.val < 777 then alphaSourceLiteral776 else alphaSourceLiteral777) else (if i.val < 779 then alphaSourceLiteral778 else alphaSourceLiteral779)) else (if i.val < 782 then (if i.val < 781 then alphaSourceLiteral780 else alphaSourceLiteral781) else (if i.val < 783 then alphaSourceLiteral782 else alphaSourceLiteral783)))) else (if i.val < 792 then (if i.val < 788 then (if i.val < 786 then (if i.val < 785 then alphaSourceLiteral784 else alphaSourceLiteral785) else (if i.val < 787 then alphaSourceLiteral786 else alphaSourceLiteral787)) else (if i.val < 790 then (if i.val < 789 then alphaSourceLiteral788 else alphaSourceLiteral789) else (if i.val < 791 then alphaSourceLiteral790 else alphaSourceLiteral791))) else (if i.val < 796 then (if i.val < 794 then (if i.val < 793 then alphaSourceLiteral792 else alphaSourceLiteral793) else (if i.val < 795 then alphaSourceLiteral794 else alphaSourceLiteral795)) else (if i.val < 798 then (if i.val < 797 then alphaSourceLiteral796 else alphaSourceLiteral797) else (if i.val < 799 then alphaSourceLiteral798 else alphaSourceLiteral799))))) else (if i.val < 816 then (if i.val < 808 then (if i.val < 804 then (if i.val < 802 then (if i.val < 801 then alphaSourceLiteral800 else alphaSourceLiteral801) else (if i.val < 803 then alphaSourceLiteral802 else alphaSourceLiteral803)) else (if i.val < 806 then (if i.val < 805 then alphaSourceLiteral804 else alphaSourceLiteral805) else (if i.val < 807 then alphaSourceLiteral806 else alphaSourceLiteral807))) else (if i.val < 812 then (if i.val < 810 then (if i.val < 809 then alphaSourceLiteral808 else alphaSourceLiteral809) else (if i.val < 811 then alphaSourceLiteral810 else alphaSourceLiteral811)) else (if i.val < 814 then (if i.val < 813 then alphaSourceLiteral812 else alphaSourceLiteral813) else (if i.val < 815 then alphaSourceLiteral814 else alphaSourceLiteral815)))) else (if i.val < 824 then (if i.val < 820 then (if i.val < 818 then (if i.val < 817 then alphaSourceLiteral816 else alphaSourceLiteral817) else (if i.val < 819 then alphaSourceLiteral818 else alphaSourceLiteral819)) else (if i.val < 822 then (if i.val < 821 then alphaSourceLiteral820 else alphaSourceLiteral821) else (if i.val < 823 then alphaSourceLiteral822 else alphaSourceLiteral823))) else (if i.val < 828 then (if i.val < 826 then (if i.val < 825 then alphaSourceLiteral824 else alphaSourceLiteral825) else (if i.val < 827 then alphaSourceLiteral826 else alphaSourceLiteral827)) else (if i.val < 830 then (if i.val < 829 then alphaSourceLiteral828 else alphaSourceLiteral829) else (if i.val < 831 then alphaSourceLiteral830 else alphaSourceLiteral831)))))) else (if i.val < 864 then (if i.val < 848 then (if i.val < 840 then (if i.val < 836 then (if i.val < 834 then (if i.val < 833 then alphaSourceLiteral832 else alphaSourceLiteral833) else (if i.val < 835 then alphaSourceLiteral834 else alphaSourceLiteral835)) else (if i.val < 838 then (if i.val < 837 then alphaSourceLiteral836 else alphaSourceLiteral837) else (if i.val < 839 then alphaSourceLiteral838 else alphaSourceLiteral839))) else (if i.val < 844 then (if i.val < 842 then (if i.val < 841 then alphaSourceLiteral840 else alphaSourceLiteral841) else (if i.val < 843 then alphaSourceLiteral842 else alphaSourceLiteral843)) else (if i.val < 846 then (if i.val < 845 then alphaSourceLiteral844 else alphaSourceLiteral845) else (if i.val < 847 then alphaSourceLiteral846 else alphaSourceLiteral847)))) else (if i.val < 856 then (if i.val < 852 then (if i.val < 850 then (if i.val < 849 then alphaSourceLiteral848 else alphaSourceLiteral849) else (if i.val < 851 then alphaSourceLiteral850 else alphaSourceLiteral851)) else (if i.val < 854 then (if i.val < 853 then alphaSourceLiteral852 else alphaSourceLiteral853) else (if i.val < 855 then alphaSourceLiteral854 else alphaSourceLiteral855))) else (if i.val < 860 then (if i.val < 858 then (if i.val < 857 then alphaSourceLiteral856 else alphaSourceLiteral857) else (if i.val < 859 then alphaSourceLiteral858 else alphaSourceLiteral859)) else (if i.val < 862 then (if i.val < 861 then alphaSourceLiteral860 else alphaSourceLiteral861) else (if i.val < 863 then alphaSourceLiteral862 else alphaSourceLiteral863))))) else (if i.val < 880 then (if i.val < 872 then (if i.val < 868 then (if i.val < 866 then (if i.val < 865 then alphaSourceLiteral864 else alphaSourceLiteral865) else (if i.val < 867 then alphaSourceLiteral866 else alphaSourceLiteral867)) else (if i.val < 870 then (if i.val < 869 then alphaSourceLiteral868 else alphaSourceLiteral869) else (if i.val < 871 then alphaSourceLiteral870 else alphaSourceLiteral871))) else (if i.val < 876 then (if i.val < 874 then (if i.val < 873 then alphaSourceLiteral872 else alphaSourceLiteral873) else (if i.val < 875 then alphaSourceLiteral874 else alphaSourceLiteral875)) else (if i.val < 878 then (if i.val < 877 then alphaSourceLiteral876 else alphaSourceLiteral877) else (if i.val < 879 then alphaSourceLiteral878 else alphaSourceLiteral879)))) else (if i.val < 888 then (if i.val < 884 then (if i.val < 882 then (if i.val < 881 then alphaSourceLiteral880 else alphaSourceLiteral881) else (if i.val < 883 then alphaSourceLiteral882 else alphaSourceLiteral883)) else (if i.val < 886 then (if i.val < 885 then alphaSourceLiteral884 else alphaSourceLiteral885) else (if i.val < 887 then alphaSourceLiteral886 else alphaSourceLiteral887))) else (if i.val < 892 then (if i.val < 890 then (if i.val < 889 then alphaSourceLiteral888 else alphaSourceLiteral889) else (if i.val < 891 then alphaSourceLiteral890 else alphaSourceLiteral891)) else (if i.val < 894 then (if i.val < 893 then alphaSourceLiteral892 else alphaSourceLiteral893) else (if i.val < 895 then alphaSourceLiteral894 else alphaSourceLiteral895))))))) else (if i.val < 960 then (if i.val < 928 then (if i.val < 912 then (if i.val < 904 then (if i.val < 900 then (if i.val < 898 then (if i.val < 897 then alphaSourceLiteral896 else alphaSourceLiteral897) else (if i.val < 899 then alphaSourceLiteral898 else alphaSourceLiteral899)) else (if i.val < 902 then (if i.val < 901 then alphaSourceLiteral900 else alphaSourceLiteral901) else (if i.val < 903 then alphaSourceLiteral902 else alphaSourceLiteral903))) else (if i.val < 908 then (if i.val < 906 then (if i.val < 905 then alphaSourceLiteral904 else alphaSourceLiteral905) else (if i.val < 907 then alphaSourceLiteral906 else alphaSourceLiteral907)) else (if i.val < 910 then (if i.val < 909 then alphaSourceLiteral908 else alphaSourceLiteral909) else (if i.val < 911 then alphaSourceLiteral910 else alphaSourceLiteral911)))) else (if i.val < 920 then (if i.val < 916 then (if i.val < 914 then (if i.val < 913 then alphaSourceLiteral912 else alphaSourceLiteral913) else (if i.val < 915 then alphaSourceLiteral914 else alphaSourceLiteral915)) else (if i.val < 918 then (if i.val < 917 then alphaSourceLiteral916 else alphaSourceLiteral917) else (if i.val < 919 then alphaSourceLiteral918 else alphaSourceLiteral919))) else (if i.val < 924 then (if i.val < 922 then (if i.val < 921 then alphaSourceLiteral920 else alphaSourceLiteral921) else (if i.val < 923 then alphaSourceLiteral922 else alphaSourceLiteral923)) else (if i.val < 926 then (if i.val < 925 then alphaSourceLiteral924 else alphaSourceLiteral925) else (if i.val < 927 then alphaSourceLiteral926 else alphaSourceLiteral927))))) else (if i.val < 944 then (if i.val < 936 then (if i.val < 932 then (if i.val < 930 then (if i.val < 929 then alphaSourceLiteral928 else alphaSourceLiteral929) else (if i.val < 931 then alphaSourceLiteral930 else alphaSourceLiteral931)) else (if i.val < 934 then (if i.val < 933 then alphaSourceLiteral932 else alphaSourceLiteral933) else (if i.val < 935 then alphaSourceLiteral934 else alphaSourceLiteral935))) else (if i.val < 940 then (if i.val < 938 then (if i.val < 937 then alphaSourceLiteral936 else alphaSourceLiteral937) else (if i.val < 939 then alphaSourceLiteral938 else alphaSourceLiteral939)) else (if i.val < 942 then (if i.val < 941 then alphaSourceLiteral940 else alphaSourceLiteral941) else (if i.val < 943 then alphaSourceLiteral942 else alphaSourceLiteral943)))) else (if i.val < 952 then (if i.val < 948 then (if i.val < 946 then (if i.val < 945 then alphaSourceLiteral944 else alphaSourceLiteral945) else (if i.val < 947 then alphaSourceLiteral946 else alphaSourceLiteral947)) else (if i.val < 950 then (if i.val < 949 then alphaSourceLiteral948 else alphaSourceLiteral949) else (if i.val < 951 then alphaSourceLiteral950 else alphaSourceLiteral951))) else (if i.val < 956 then (if i.val < 954 then (if i.val < 953 then alphaSourceLiteral952 else alphaSourceLiteral953) else (if i.val < 955 then alphaSourceLiteral954 else alphaSourceLiteral955)) else (if i.val < 958 then (if i.val < 957 then alphaSourceLiteral956 else alphaSourceLiteral957) else (if i.val < 959 then alphaSourceLiteral958 else alphaSourceLiteral959)))))) else (if i.val < 992 then (if i.val < 976 then (if i.val < 968 then (if i.val < 964 then (if i.val < 962 then (if i.val < 961 then alphaSourceLiteral960 else alphaSourceLiteral961) else (if i.val < 963 then alphaSourceLiteral962 else alphaSourceLiteral963)) else (if i.val < 966 then (if i.val < 965 then alphaSourceLiteral964 else alphaSourceLiteral965) else (if i.val < 967 then alphaSourceLiteral966 else alphaSourceLiteral967))) else (if i.val < 972 then (if i.val < 970 then (if i.val < 969 then alphaSourceLiteral968 else alphaSourceLiteral969) else (if i.val < 971 then alphaSourceLiteral970 else alphaSourceLiteral971)) else (if i.val < 974 then (if i.val < 973 then alphaSourceLiteral972 else alphaSourceLiteral973) else (if i.val < 975 then alphaSourceLiteral974 else alphaSourceLiteral975)))) else (if i.val < 984 then (if i.val < 980 then (if i.val < 978 then (if i.val < 977 then alphaSourceLiteral976 else alphaSourceLiteral977) else (if i.val < 979 then alphaSourceLiteral978 else alphaSourceLiteral979)) else (if i.val < 982 then (if i.val < 981 then alphaSourceLiteral980 else alphaSourceLiteral981) else (if i.val < 983 then alphaSourceLiteral982 else alphaSourceLiteral983))) else (if i.val < 988 then (if i.val < 986 then (if i.val < 985 then alphaSourceLiteral984 else alphaSourceLiteral985) else (if i.val < 987 then alphaSourceLiteral986 else alphaSourceLiteral987)) else (if i.val < 990 then (if i.val < 989 then alphaSourceLiteral988 else alphaSourceLiteral989) else (if i.val < 991 then alphaSourceLiteral990 else alphaSourceLiteral991))))) else (if i.val < 1008 then (if i.val < 1000 then (if i.val < 996 then (if i.val < 994 then (if i.val < 993 then alphaSourceLiteral992 else alphaSourceLiteral993) else (if i.val < 995 then alphaSourceLiteral994 else alphaSourceLiteral995)) else (if i.val < 998 then (if i.val < 997 then alphaSourceLiteral996 else alphaSourceLiteral997) else (if i.val < 999 then alphaSourceLiteral998 else alphaSourceLiteral999))) else (if i.val < 1004 then (if i.val < 1002 then (if i.val < 1001 then alphaSourceLiteral1000 else alphaSourceLiteral1001) else (if i.val < 1003 then alphaSourceLiteral1002 else alphaSourceLiteral1003)) else (if i.val < 1006 then (if i.val < 1005 then alphaSourceLiteral1004 else alphaSourceLiteral1005) else (if i.val < 1007 then alphaSourceLiteral1006 else alphaSourceLiteral1007)))) else (if i.val < 1016 then (if i.val < 1012 then (if i.val < 1010 then (if i.val < 1009 then alphaSourceLiteral1008 else alphaSourceLiteral1009) else (if i.val < 1011 then alphaSourceLiteral1010 else alphaSourceLiteral1011)) else (if i.val < 1014 then (if i.val < 1013 then alphaSourceLiteral1012 else alphaSourceLiteral1013) else (if i.val < 1015 then alphaSourceLiteral1014 else alphaSourceLiteral1015))) else (if i.val < 1020 then (if i.val < 1018 then (if i.val < 1017 then alphaSourceLiteral1016 else alphaSourceLiteral1017) else (if i.val < 1019 then alphaSourceLiteral1018 else alphaSourceLiteral1019)) else (if i.val < 1022 then (if i.val < 1021 then alphaSourceLiteral1020 else alphaSourceLiteral1021) else (if i.val < 1023 then alphaSourceLiteral1022 else alphaSourceLiteral1023))))))))))

private def alphaTargetLiteral0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral3 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral4 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral5 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral6 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral7 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral8 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral9 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral10 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral11 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral12 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral13 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral14 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral15 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral16 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral17 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral18 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral19 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral20 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral21 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral22 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral23 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral24 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral25 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral26 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral27 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral28 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral29 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral30 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral31 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral32 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral33 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral34 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral35 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral36 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral37 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral38 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral39 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral40 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral41 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral42 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral43 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral44 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral45 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral46 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral47 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral48 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral49 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral50 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral51 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral52 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral53 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral54 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral55 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral56 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral57 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral58 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral59 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral60 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral61 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral62 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral63 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral64 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral65 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral66 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral67 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral68 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral69 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral70 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral71 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral72 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral73 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral74 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral75 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral76 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral77 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral78 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral79 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral80 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral81 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral82 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral83 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral84 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral85 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral86 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral87 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral88 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral89 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral90 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral91 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral92 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral93 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral94 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral95 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral96 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral97 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral98 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral99 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral100 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral101 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral102 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral103 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral104 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral105 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral106 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral107 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral108 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral109 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral110 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral111 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral112 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral113 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral114 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral115 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral116 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral117 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral118 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral119 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral120 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral121 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral122 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral123 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral124 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral125 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral126 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral127 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral128 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral129 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral130 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral131 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral132 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral133 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral134 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral135 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral136 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral137 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral138 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral139 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral140 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral141 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral142 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral143 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral144 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral145 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral146 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral147 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral148 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral149 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral150 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral151 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral152 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral153 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral154 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral155 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral156 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral157 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral158 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral159 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral160 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral161 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral162 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral163 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral164 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral165 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral166 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral167 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral168 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral169 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral170 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral171 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral172 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral173 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral174 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral175 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral176 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral177 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral178 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral179 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral180 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral181 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral182 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral183 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral184 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral185 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral186 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral187 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral188 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral189 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral190 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral191 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral192 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral193 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral194 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral195 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral196 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral197 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral198 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral199 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral200 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral201 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral202 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral203 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral204 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral205 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral206 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral207 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral208 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral209 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral210 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral211 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral212 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral213 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral214 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral215 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral216 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral217 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral218 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral219 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral220 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral221 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral222 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral223 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral224 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral225 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral226 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral227 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral228 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral229 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral230 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral231 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral232 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral233 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral234 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral235 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral236 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral237 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral238 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral239 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral240 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral241 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral242 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral243 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral244 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral245 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral246 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral247 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral248 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral249 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral250 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral251 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral252 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral253 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral254 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTargetLiteral255 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def alphaTarget (i : Fin 1024) : Equiv.Perm (Fin 16) :=
  (if i.val < 512 then (if i.val < 256 then (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then alphaTargetLiteral0 else alphaTargetLiteral1) else (if i.val < 3 then alphaTargetLiteral2 else alphaTargetLiteral3)) else (if i.val < 6 then (if i.val < 5 then alphaTargetLiteral4 else alphaTargetLiteral5) else (if i.val < 7 then alphaTargetLiteral6 else alphaTargetLiteral7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then alphaTargetLiteral8 else alphaTargetLiteral9) else (if i.val < 11 then alphaTargetLiteral6 else alphaTargetLiteral8)) else (if i.val < 14 then (if i.val < 13 then alphaTargetLiteral0 else alphaTargetLiteral10) else (if i.val < 15 then alphaTargetLiteral11 else alphaTargetLiteral12)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then alphaTargetLiteral13 else alphaTargetLiteral14) else (if i.val < 19 then alphaTargetLiteral15 else alphaTargetLiteral16)) else (if i.val < 22 then (if i.val < 21 then alphaTargetLiteral3 else alphaTargetLiteral15) else (if i.val < 23 then alphaTargetLiteral1 else alphaTargetLiteral17))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then alphaTargetLiteral18 else alphaTargetLiteral19) else (if i.val < 27 then alphaTargetLiteral20 else alphaTargetLiteral21)) else (if i.val < 30 then (if i.val < 29 then alphaTargetLiteral15 else alphaTargetLiteral3) else (if i.val < 31 then alphaTargetLiteral2 else alphaTargetLiteral22))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then alphaTargetLiteral23 else alphaTargetLiteral24) else (if i.val < 35 then alphaTargetLiteral25 else alphaTargetLiteral26)) else (if i.val < 38 then (if i.val < 37 then alphaTargetLiteral15 else alphaTargetLiteral1) else (if i.val < 39 then alphaTargetLiteral17 else alphaTargetLiteral2))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then alphaTargetLiteral22 else alphaTargetLiteral3) else (if i.val < 43 then alphaTargetLiteral4 else alphaTargetLiteral27)) else (if i.val < 46 then (if i.val < 45 then alphaTargetLiteral28 else alphaTargetLiteral29) else (if i.val < 47 then alphaTargetLiteral30 else alphaTargetLiteral31)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then alphaTargetLiteral32 else alphaTargetLiteral33) else (if i.val < 51 then alphaTargetLiteral34 else alphaTargetLiteral35)) else (if i.val < 54 then (if i.val < 53 then alphaTargetLiteral32 else alphaTargetLiteral34) else (if i.val < 55 then alphaTargetLiteral36 else alphaTargetLiteral21))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then alphaTargetLiteral26 else alphaTargetLiteral37) else (if i.val < 59 then alphaTargetLiteral8 else alphaTargetLiteral6)) else (if i.val < 62 then (if i.val < 61 then alphaTargetLiteral5 else alphaTargetLiteral38) else (if i.val < 63 then alphaTargetLiteral39 else alphaTargetLiteral40)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then alphaTargetLiteral41 else alphaTargetLiteral42) else (if i.val < 67 then alphaTargetLiteral8 else alphaTargetLiteral0)) else (if i.val < 70 then (if i.val < 69 then alphaTargetLiteral10 else alphaTargetLiteral5) else (if i.val < 71 then alphaTargetLiteral38 else alphaTargetLiteral6))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then alphaTargetLiteral7 else alphaTargetLiteral43) else (if i.val < 75 then alphaTargetLiteral44 else alphaTargetLiteral45)) else (if i.val < 78 then (if i.val < 77 then alphaTargetLiteral46 else alphaTargetLiteral47) else (if i.val < 79 then alphaTargetLiteral48 else alphaTargetLiteral49)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then alphaTargetLiteral50 else alphaTargetLiteral51) else (if i.val < 83 then alphaTargetLiteral48 else alphaTargetLiteral50)) else (if i.val < 86 then (if i.val < 85 then alphaTargetLiteral52 else alphaTargetLiteral14) else (if i.val < 87 then alphaTargetLiteral42 else alphaTargetLiteral53))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then alphaTargetLiteral5 else alphaTargetLiteral38) else (if i.val < 91 then alphaTargetLiteral0 else alphaTargetLiteral10)) else (if i.val < 94 then (if i.val < 93 then alphaTargetLiteral9 else alphaTargetLiteral54) else (if i.val < 95 then alphaTargetLiteral55 else alphaTargetLiteral56))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then alphaTargetLiteral57 else alphaTargetLiteral58) else (if i.val < 99 then alphaTargetLiteral59 else alphaTargetLiteral60)) else (if i.val < 102 then (if i.val < 101 then alphaTargetLiteral61 else alphaTargetLiteral62) else (if i.val < 103 then alphaTargetLiteral59 else alphaTargetLiteral61))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then alphaTargetLiteral63 else alphaTargetLiteral42) else (if i.val < 107 then alphaTargetLiteral14 else alphaTargetLiteral64)) else (if i.val < 110 then (if i.val < 109 then alphaTargetLiteral38 else alphaTargetLiteral7) else (if i.val < 111 then alphaTargetLiteral43 else alphaTargetLiteral44)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then alphaTargetLiteral45 else alphaTargetLiteral46) else (if i.val < 115 then alphaTargetLiteral9 else alphaTargetLiteral54)) else (if i.val < 118 then (if i.val < 117 then alphaTargetLiteral55 else alphaTargetLiteral56) else (if i.val < 119 then alphaTargetLiteral57 else alphaTargetLiteral10))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then alphaTargetLiteral11 else alphaTargetLiteral12) else (if i.val < 123 then alphaTargetLiteral13 else alphaTargetLiteral14)) else (if i.val < 126 then (if i.val < 125 then alphaTargetLiteral65 else alphaTargetLiteral66) else (if i.val < 127 then alphaTargetLiteral67 else alphaTargetLiteral68))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then alphaTargetLiteral69 else alphaTargetLiteral66) else (if i.val < 131 then alphaTargetLiteral68 else alphaTargetLiteral70)) else (if i.val < 134 then (if i.val < 133 then alphaTargetLiteral71 else alphaTargetLiteral72) else (if i.val < 135 then alphaTargetLiteral73 else alphaTargetLiteral13))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then alphaTargetLiteral72 else alphaTargetLiteral74) else (if i.val < 139 then alphaTargetLiteral49 else alphaTargetLiteral60)) else (if i.val < 142 then (if i.val < 141 then alphaTargetLiteral67 else alphaTargetLiteral75) else (if i.val < 143 then alphaTargetLiteral72 else alphaTargetLiteral13)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then alphaTargetLiteral76 else alphaTargetLiteral51) else (if i.val < 147 then alphaTargetLiteral62 else alphaTargetLiteral77)) else (if i.val < 150 then (if i.val < 149 then alphaTargetLiteral72 else alphaTargetLiteral11) else (if i.val < 151 then alphaTargetLiteral74 else alphaTargetLiteral12))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then alphaTargetLiteral76 else alphaTargetLiteral63) else (if i.val < 155 then alphaTargetLiteral70 else alphaTargetLiteral78)) else (if i.val < 158 then (if i.val < 157 then alphaTargetLiteral42 else alphaTargetLiteral53) else (if i.val < 159 then alphaTargetLiteral64 else alphaTargetLiteral75))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then alphaTargetLiteral77 else alphaTargetLiteral2) else (if i.val < 163 then alphaTargetLiteral22 else alphaTargetLiteral1)) else (if i.val < 166 then (if i.val < 165 then alphaTargetLiteral17 else alphaTargetLiteral16) else (if i.val < 167 then alphaTargetLiteral79 else alphaTargetLiteral80))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then alphaTargetLiteral81 else alphaTargetLiteral82) else (if i.val < 171 then alphaTargetLiteral83 else alphaTargetLiteral84)) else (if i.val < 174 then (if i.val < 173 then alphaTargetLiteral85 else alphaTargetLiteral86) else (if i.val < 175 then alphaTargetLiteral87 else alphaTargetLiteral84)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then alphaTargetLiteral86 else alphaTargetLiteral88) else (if i.val < 179 then alphaTargetLiteral26 else alphaTargetLiteral21)) else (if i.val < 182 then (if i.val < 181 then alphaTargetLiteral89 else alphaTargetLiteral22) else (if i.val < 183 then alphaTargetLiteral4 else alphaTargetLiteral27))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then alphaTargetLiteral28 else alphaTargetLiteral29) else (if i.val < 187 then alphaTargetLiteral30 else alphaTargetLiteral16)) else (if i.val < 190 then (if i.val < 189 then alphaTargetLiteral79 else alphaTargetLiteral80) else (if i.val < 191 then alphaTargetLiteral81 else alphaTargetLiteral82)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then alphaTargetLiteral17 else alphaTargetLiteral18) else (if i.val < 195 then alphaTargetLiteral19 else alphaTargetLiteral20)) else (if i.val < 198 then (if i.val < 197 then alphaTargetLiteral21 else alphaTargetLiteral90) else (if i.val < 199 then alphaTargetLiteral91 else alphaTargetLiteral92))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then alphaTargetLiteral93 else alphaTargetLiteral94) else (if i.val < 203 then alphaTargetLiteral91 else alphaTargetLiteral93)) else (if i.val < 206 then (if i.val < 205 then alphaTargetLiteral95 else alphaTargetLiteral96) else (if i.val < 207 then alphaTargetLiteral97 else alphaTargetLiteral98)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then alphaTargetLiteral20 else alphaTargetLiteral97) else (if i.val < 211 then alphaTargetLiteral99 else alphaTargetLiteral33)) else (if i.val < 214 then (if i.val < 213 then alphaTargetLiteral85 else alphaTargetLiteral92) else (if i.val < 215 then alphaTargetLiteral100 else alphaTargetLiteral97))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then alphaTargetLiteral20 else alphaTargetLiteral101) else (if i.val < 219 then alphaTargetLiteral35 else alphaTargetLiteral87)) else (if i.val < 222 then (if i.val < 221 then alphaTargetLiteral102 else alphaTargetLiteral97) else (if i.val < 223 then alphaTargetLiteral18 else alphaTargetLiteral99))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then alphaTargetLiteral19 else alphaTargetLiteral101) else (if i.val < 227 then alphaTargetLiteral88 else alphaTargetLiteral95)) else (if i.val < 230 then (if i.val < 229 then alphaTargetLiteral103 else alphaTargetLiteral26) else (if i.val < 231 then alphaTargetLiteral37 else alphaTargetLiteral89))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then alphaTargetLiteral100 else alphaTargetLiteral102) else (if i.val < 235 then alphaTargetLiteral16 else alphaTargetLiteral79)) else (if i.val < 238 then (if i.val < 237 then alphaTargetLiteral80 else alphaTargetLiteral81) else (if i.val < 239 then alphaTargetLiteral82 else alphaTargetLiteral4)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then alphaTargetLiteral27 else alphaTargetLiteral28) else (if i.val < 243 then alphaTargetLiteral29 else alphaTargetLiteral30)) else (if i.val < 246 then (if i.val < 245 then alphaTargetLiteral23 else alphaTargetLiteral24) else (if i.val < 247 then alphaTargetLiteral25 else alphaTargetLiteral104))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then alphaTargetLiteral105 else alphaTargetLiteral106) else (if i.val < 251 then alphaTargetLiteral107 else alphaTargetLiteral108)) else (if i.val < 254 then (if i.val < 253 then alphaTargetLiteral105 else alphaTargetLiteral107) else (if i.val < 255 then alphaTargetLiteral109 else alphaTargetLiteral110)))))))) else (if i.val < 384 then (if i.val < 320 then (if i.val < 288 then (if i.val < 272 then (if i.val < 264 then (if i.val < 260 then (if i.val < 258 then (if i.val < 257 then alphaTargetLiteral111 else alphaTargetLiteral112) else (if i.val < 259 then alphaTargetLiteral25 else alphaTargetLiteral111)) else (if i.val < 262 then (if i.val < 261 then alphaTargetLiteral113 else alphaTargetLiteral85) else (if i.val < 263 then alphaTargetLiteral33 else alphaTargetLiteral106))) else (if i.val < 268 then (if i.val < 266 then (if i.val < 265 then alphaTargetLiteral114 else alphaTargetLiteral111) else (if i.val < 267 then alphaTargetLiteral25 else alphaTargetLiteral115)) else (if i.val < 270 then (if i.val < 269 then alphaTargetLiteral87 else alphaTargetLiteral35) else (if i.val < 271 then alphaTargetLiteral116 else alphaTargetLiteral111)))) else (if i.val < 280 then (if i.val < 276 then (if i.val < 274 then (if i.val < 273 then alphaTargetLiteral23 else alphaTargetLiteral113) else (if i.val < 275 then alphaTargetLiteral24 else alphaTargetLiteral115)) else (if i.val < 278 then (if i.val < 277 then alphaTargetLiteral36 else alphaTargetLiteral109) else (if i.val < 279 then alphaTargetLiteral117 else alphaTargetLiteral89))) else (if i.val < 284 then (if i.val < 282 then (if i.val < 281 then alphaTargetLiteral37 else alphaTargetLiteral114) else (if i.val < 283 then alphaTargetLiteral116 else alphaTargetLiteral79)) else (if i.val < 286 then (if i.val < 285 then alphaTargetLiteral80 else alphaTargetLiteral81) else (if i.val < 287 then alphaTargetLiteral82 else alphaTargetLiteral18))))) else (if i.val < 304 then (if i.val < 296 then (if i.val < 292 then (if i.val < 290 then (if i.val < 289 then alphaTargetLiteral90 else alphaTargetLiteral91) else (if i.val < 291 then alphaTargetLiteral92 else alphaTargetLiteral94)) else (if i.val < 294 then (if i.val < 293 then alphaTargetLiteral91 else alphaTargetLiteral95) else (if i.val < 295 then alphaTargetLiteral96 else alphaTargetLiteral24))) else (if i.val < 300 then (if i.val < 298 then (if i.val < 297 then alphaTargetLiteral104 else alphaTargetLiteral107) else (if i.val < 299 then alphaTargetLiteral108 else alphaTargetLiteral107)) else (if i.val < 302 then (if i.val < 301 then alphaTargetLiteral109 else alphaTargetLiteral110) else (if i.val < 303 then alphaTargetLiteral27 else alphaTargetLiteral28)))) else (if i.val < 312 then (if i.val < 308 then (if i.val < 306 then (if i.val < 305 then alphaTargetLiteral29 else alphaTargetLiteral30) else (if i.val < 307 then alphaTargetLiteral31 else alphaTargetLiteral32)) else (if i.val < 310 then (if i.val < 309 then alphaTargetLiteral33 else alphaTargetLiteral34) else (if i.val < 311 then alphaTargetLiteral35 else alphaTargetLiteral32))) else (if i.val < 316 then (if i.val < 314 then (if i.val < 313 then alphaTargetLiteral34 else alphaTargetLiteral36) else (if i.val < 315 then alphaTargetLiteral37 else alphaTargetLiteral118)) else (if i.val < 318 then (if i.val < 317 then alphaTargetLiteral119 else alphaTargetLiteral118) else (if i.val < 319 then alphaTargetLiteral120 else alphaTargetLiteral121)))))) else (if i.val < 352 then (if i.val < 336 then (if i.val < 328 then (if i.val < 324 then (if i.val < 322 then (if i.val < 321 then alphaTargetLiteral118 else alphaTargetLiteral122) else (if i.val < 323 then alphaTargetLiteral123 else alphaTargetLiteral118)) else (if i.val < 326 then (if i.val < 325 then alphaTargetLiteral120 else alphaTargetLiteral122) else (if i.val < 327 then alphaTargetLiteral124 else alphaTargetLiteral121))) else (if i.val < 332 then (if i.val < 330 then (if i.val < 329 then alphaTargetLiteral123 else alphaTargetLiteral125) else (if i.val < 331 then alphaTargetLiteral98 else alphaTargetLiteral112)) else (if i.val < 334 then (if i.val < 333 then alphaTargetLiteral119 else alphaTargetLiteral126) else (if i.val < 335 then alphaTargetLiteral31 else alphaTargetLiteral125)))) else (if i.val < 344 then (if i.val < 340 then (if i.val < 338 then (if i.val < 337 then alphaTargetLiteral120 else alphaTargetLiteral127) else (if i.val < 339 then alphaTargetLiteral85 else alphaTargetLiteral92)) else (if i.val < 342 then (if i.val < 341 then alphaTargetLiteral100 else alphaTargetLiteral126) else (if i.val < 343 then alphaTargetLiteral128 else alphaTargetLiteral31))) else (if i.val < 348 then (if i.val < 346 then (if i.val < 345 then alphaTargetLiteral125 else alphaTargetLiteral36) else (if i.val < 347 then alphaTargetLiteral115 else alphaTargetLiteral122)) else (if i.val < 350 then (if i.val < 349 then alphaTargetLiteral129 else alphaTargetLiteral87) else (if i.val < 351 then alphaTargetLiteral116 else alphaTargetLiteral126))))) else (if i.val < 368 then (if i.val < 360 then (if i.val < 356 then (if i.val < 354 then (if i.val < 353 then alphaTargetLiteral130 else alphaTargetLiteral125) else (if i.val < 355 then alphaTargetLiteral120 else alphaTargetLiteral127)) else (if i.val < 358 then (if i.val < 357 then alphaTargetLiteral115 else alphaTargetLiteral122) else (if i.val < 359 then alphaTargetLiteral129 else alphaTargetLiteral109))) else (if i.val < 364 then (if i.val < 362 then (if i.val < 361 then alphaTargetLiteral117 else alphaTargetLiteral95) else (if i.val < 363 then alphaTargetLiteral124 else alphaTargetLiteral131)) else (if i.val < 366 then (if i.val < 365 then alphaTargetLiteral89 else alphaTargetLiteral100) else (if i.val < 367 then alphaTargetLiteral103 else alphaTargetLiteral116)))) else (if i.val < 376 then (if i.val < 372 then (if i.val < 370 then (if i.val < 369 then alphaTargetLiteral126 else alphaTargetLiteral128) else (if i.val < 371 then alphaTargetLiteral130 else alphaTargetLiteral9)) else (if i.val < 374 then (if i.val < 373 then alphaTargetLiteral54 else alphaTargetLiteral55) else (if i.val < 375 then alphaTargetLiteral56 else alphaTargetLiteral57))) else (if i.val < 380 then (if i.val < 378 then (if i.val < 377 then alphaTargetLiteral7 else alphaTargetLiteral43) else (if i.val < 379 then alphaTargetLiteral44 else alphaTargetLiteral45)) else (if i.val < 382 then (if i.val < 381 then alphaTargetLiteral46 else alphaTargetLiteral39) else (if i.val < 383 then alphaTargetLiteral40 else alphaTargetLiteral41))))))) else (if i.val < 448 then (if i.val < 416 then (if i.val < 400 then (if i.val < 392 then (if i.val < 388 then (if i.val < 386 then (if i.val < 385 then alphaTargetLiteral132 else alphaTargetLiteral133) else (if i.val < 387 then alphaTargetLiteral134 else alphaTargetLiteral135)) else (if i.val < 390 then (if i.val < 389 then alphaTargetLiteral136 else alphaTargetLiteral133) else (if i.val < 391 then alphaTargetLiteral135 else alphaTargetLiteral137))) else (if i.val < 396 then (if i.val < 394 then (if i.val < 393 then alphaTargetLiteral138 else alphaTargetLiteral139) else (if i.val < 395 then alphaTargetLiteral140 else alphaTargetLiteral41)) else (if i.val < 398 then (if i.val < 397 then alphaTargetLiteral139 else alphaTargetLiteral141) else (if i.val < 399 then alphaTargetLiteral60 else alphaTargetLiteral49)))) else (if i.val < 408 then (if i.val < 404 then (if i.val < 402 then (if i.val < 401 then alphaTargetLiteral134 else alphaTargetLiteral142) else (if i.val < 403 then alphaTargetLiteral139 else alphaTargetLiteral41)) else (if i.val < 406 then (if i.val < 405 then alphaTargetLiteral143 else alphaTargetLiteral62) else (if i.val < 407 then alphaTargetLiteral51 else alphaTargetLiteral144))) else (if i.val < 412 then (if i.val < 410 then (if i.val < 409 then alphaTargetLiteral139 else alphaTargetLiteral39) else (if i.val < 411 then alphaTargetLiteral141 else alphaTargetLiteral40)) else (if i.val < 414 then (if i.val < 413 then alphaTargetLiteral143 else alphaTargetLiteral52) else (if i.val < 415 then alphaTargetLiteral137 else alphaTargetLiteral145))))) else (if i.val < 432 then (if i.val < 424 then (if i.val < 420 then (if i.val < 418 then (if i.val < 417 then alphaTargetLiteral64 else alphaTargetLiteral53) else (if i.val < 419 then alphaTargetLiteral142 else alphaTargetLiteral144)) else (if i.val < 422 then (if i.val < 421 then alphaTargetLiteral54 else alphaTargetLiteral55) else (if i.val < 423 then alphaTargetLiteral56 else alphaTargetLiteral57))) else (if i.val < 428 then (if i.val < 426 then (if i.val < 425 then alphaTargetLiteral11 else alphaTargetLiteral65) else (if i.val < 427 then alphaTargetLiteral66 else alphaTargetLiteral67)) else (if i.val < 430 then (if i.val < 429 then alphaTargetLiteral69 else alphaTargetLiteral66) else (if i.val < 431 then alphaTargetLiteral70 else alphaTargetLiteral71)))) else (if i.val < 440 then (if i.val < 436 then (if i.val < 434 then (if i.val < 433 then alphaTargetLiteral40 else alphaTargetLiteral132) else (if i.val < 435 then alphaTargetLiteral135 else alphaTargetLiteral136)) else (if i.val < 438 then (if i.val < 437 then alphaTargetLiteral135 else alphaTargetLiteral137) else (if i.val < 439 then alphaTargetLiteral138 else alphaTargetLiteral43))) else (if i.val < 444 then (if i.val < 442 then (if i.val < 441 then alphaTargetLiteral44 else alphaTargetLiteral45) else (if i.val < 443 then alphaTargetLiteral46 else alphaTargetLiteral47)) else (if i.val < 446 then (if i.val < 445 then alphaTargetLiteral48 else alphaTargetLiteral49) else (if i.val < 447 then alphaTargetLiteral50 else alphaTargetLiteral51)))))) else (if i.val < 480 then (if i.val < 464 then (if i.val < 456 then (if i.val < 452 then (if i.val < 450 then (if i.val < 449 then alphaTargetLiteral48 else alphaTargetLiteral50) else (if i.val < 451 then alphaTargetLiteral52 else alphaTargetLiteral53)) else (if i.val < 454 then (if i.val < 453 then alphaTargetLiteral146 else alphaTargetLiteral147) else (if i.val < 455 then alphaTargetLiteral146 else alphaTargetLiteral148))) else (if i.val < 460 then (if i.val < 458 then (if i.val < 457 then alphaTargetLiteral149 else alphaTargetLiteral146) else (if i.val < 459 then alphaTargetLiteral150 else alphaTargetLiteral151)) else (if i.val < 462 then (if i.val < 461 then alphaTargetLiteral146 else alphaTargetLiteral148) else (if i.val < 463 then alphaTargetLiteral150 else alphaTargetLiteral152)))) else (if i.val < 472 then (if i.val < 468 then (if i.val < 466 then (if i.val < 465 then alphaTargetLiteral149 else alphaTargetLiteral151) else (if i.val < 467 then alphaTargetLiteral153 else alphaTargetLiteral73)) else (if i.val < 470 then (if i.val < 469 then alphaTargetLiteral140 else alphaTargetLiteral147) else (if i.val < 471 then alphaTargetLiteral154 else alphaTargetLiteral47))) else (if i.val < 476 then (if i.val < 474 then (if i.val < 473 then alphaTargetLiteral153 else alphaTargetLiteral148) else (if i.val < 475 then alphaTargetLiteral155 else alphaTargetLiteral60)) else (if i.val < 478 then (if i.val < 477 then alphaTargetLiteral67 else alphaTargetLiteral75) else (if i.val < 479 then alphaTargetLiteral154 else alphaTargetLiteral156))))) else (if i.val < 496 then (if i.val < 488 then (if i.val < 484 then (if i.val < 482 then (if i.val < 481 then alphaTargetLiteral47 else alphaTargetLiteral153) else (if i.val < 483 then alphaTargetLiteral52 else alphaTargetLiteral143)) else (if i.val < 486 then (if i.val < 485 then alphaTargetLiteral150 else alphaTargetLiteral157) else (if i.val < 487 then alphaTargetLiteral62 else alphaTargetLiteral144))) else (if i.val < 492 then (if i.val < 490 then (if i.val < 489 then alphaTargetLiteral154 else alphaTargetLiteral158) else (if i.val < 491 then alphaTargetLiteral153 else alphaTargetLiteral148)) else (if i.val < 494 then (if i.val < 493 then alphaTargetLiteral155 else alphaTargetLiteral143) else (if i.val < 495 then alphaTargetLiteral150 else alphaTargetLiteral157)))) else (if i.val < 504 then (if i.val < 500 then (if i.val < 498 then (if i.val < 497 then alphaTargetLiteral137 else alphaTargetLiteral145) else (if i.val < 499 then alphaTargetLiteral70 else alphaTargetLiteral152)) else (if i.val < 502 then (if i.val < 501 then alphaTargetLiteral159 else alphaTargetLiteral64) else (if i.val < 503 then alphaTargetLiteral75 else alphaTargetLiteral78))) else (if i.val < 508 then (if i.val < 506 then (if i.val < 505 then alphaTargetLiteral144 else alphaTargetLiteral154) else (if i.val < 507 then alphaTargetLiteral156 else alphaTargetLiteral158)) else (if i.val < 510 then (if i.val < 509 then alphaTargetLiteral39 else alphaTargetLiteral132) else (if i.val < 511 then alphaTargetLiteral133 else alphaTargetLiteral134))))))))) else (if i.val < 768 then (if i.val < 640 then (if i.val < 576 then (if i.val < 544 then (if i.val < 528 then (if i.val < 520 then (if i.val < 516 then (if i.val < 514 then (if i.val < 513 then alphaTargetLiteral136 else alphaTargetLiteral133) else (if i.val < 515 then alphaTargetLiteral138 else alphaTargetLiteral12)) else (if i.val < 518 then (if i.val < 517 then alphaTargetLiteral65 else alphaTargetLiteral68) else (if i.val < 519 then alphaTargetLiteral69 else alphaTargetLiteral68))) else (if i.val < 524 then (if i.val < 522 then (if i.val < 521 then alphaTargetLiteral71 else alphaTargetLiteral58) else (if i.val < 523 then alphaTargetLiteral59 else alphaTargetLiteral61)) else (if i.val < 526 then (if i.val < 525 then alphaTargetLiteral59 else alphaTargetLiteral61) else (if i.val < 527 then alphaTargetLiteral63 else alphaTargetLiteral160)))) else (if i.val < 536 then (if i.val < 532 then (if i.val < 530 then (if i.val < 529 then alphaTargetLiteral161 else alphaTargetLiteral160) else (if i.val < 531 then alphaTargetLiteral162 else alphaTargetLiteral163)) else (if i.val < 534 then (if i.val < 533 then alphaTargetLiteral160 else alphaTargetLiteral164) else (if i.val < 535 then alphaTargetLiteral165 else alphaTargetLiteral160))) else (if i.val < 540 then (if i.val < 538 then (if i.val < 537 then alphaTargetLiteral162 else alphaTargetLiteral164) else (if i.val < 539 then alphaTargetLiteral166 else alphaTargetLiteral163)) else (if i.val < 542 then (if i.val < 541 then alphaTargetLiteral165 else alphaTargetLiteral167) else (if i.val < 543 then alphaTargetLiteral140 else alphaTargetLiteral73))))) else (if i.val < 560 then (if i.val < 552 then (if i.val < 548 then (if i.val < 546 then (if i.val < 545 then alphaTargetLiteral161 else alphaTargetLiteral168) else (if i.val < 547 then alphaTargetLiteral58 else alphaTargetLiteral167)) else (if i.val < 550 then (if i.val < 549 then alphaTargetLiteral162 else alphaTargetLiteral169) else (if i.val < 551 then alphaTargetLiteral134 else alphaTargetLiteral142))) else (if i.val < 556 then (if i.val < 554 then (if i.val < 553 then alphaTargetLiteral168 else alphaTargetLiteral170) else (if i.val < 555 then alphaTargetLiteral58 else alphaTargetLiteral167)) else (if i.val < 558 then (if i.val < 557 then alphaTargetLiteral63 else alphaTargetLiteral76) else (if i.val < 559 then alphaTargetLiteral164 else alphaTargetLiteral171)))) else (if i.val < 568 then (if i.val < 564 then (if i.val < 562 then (if i.val < 561 then alphaTargetLiteral77 else alphaTargetLiteral168) else (if i.val < 563 then alphaTargetLiteral172 else alphaTargetLiteral167)) else (if i.val < 566 then (if i.val < 565 then alphaTargetLiteral162 else alphaTargetLiteral169) else (if i.val < 567 then alphaTargetLiteral76 else alphaTargetLiteral164))) else (if i.val < 572 then (if i.val < 570 then (if i.val < 569 then alphaTargetLiteral171 else alphaTargetLiteral78) else (if i.val < 571 then alphaTargetLiteral166 else alphaTargetLiteral173)) else (if i.val < 574 then (if i.val < 573 then alphaTargetLiteral142 else alphaTargetLiteral145) else (if i.val < 575 then alphaTargetLiteral77 else alphaTargetLiteral168)))))) else (if i.val < 608 then (if i.val < 592 then (if i.val < 584 then (if i.val < 580 then (if i.val < 578 then (if i.val < 577 then alphaTargetLiteral170 else alphaTargetLiteral172) else (if i.val < 579 then alphaTargetLiteral132 else alphaTargetLiteral136)) else (if i.val < 582 then (if i.val < 581 then alphaTargetLiteral138 else alphaTargetLiteral147) else (if i.val < 583 then alphaTargetLiteral149 else alphaTargetLiteral152))) else (if i.val < 588 then (if i.val < 586 then (if i.val < 585 then alphaTargetLiteral149 else alphaTargetLiteral165) else (if i.val < 587 then alphaTargetLiteral166 else alphaTargetLiteral165)) else (if i.val < 590 then (if i.val < 589 then alphaTargetLiteral65 else alphaTargetLiteral69) else (if i.val < 591 then alphaTargetLiteral71 else alphaTargetLiteral73)))) else (if i.val < 600 then (if i.val < 596 then (if i.val < 594 then (if i.val < 593 then alphaTargetLiteral74 else alphaTargetLiteral74) else (if i.val < 595 then alphaTargetLiteral78 else alphaTargetLiteral174)) else (if i.val < 598 then (if i.val < 597 then alphaTargetLiteral175 else alphaTargetLiteral174) else (if i.val < 599 then alphaTargetLiteral176 else alphaTargetLiteral175))) else (if i.val < 604 then (if i.val < 602 then (if i.val < 601 then alphaTargetLiteral177 else alphaTargetLiteral174) else (if i.val < 603 then alphaTargetLiteral178 else alphaTargetLiteral175)) else (if i.val < 606 then (if i.val < 605 then alphaTargetLiteral179 else alphaTargetLiteral174) else (if i.val < 607 then alphaTargetLiteral176 else alphaTargetLiteral178))))) else (if i.val < 624 then (if i.val < 616 then (if i.val < 612 then (if i.val < 610 then (if i.val < 609 then alphaTargetLiteral180 else alphaTargetLiteral175) else (if i.val < 611 then alphaTargetLiteral177 else alphaTargetLiteral179)) else (if i.val < 614 then (if i.val < 613 then alphaTargetLiteral181 else alphaTargetLiteral140) else (if i.val < 615 then alphaTargetLiteral147 else alphaTargetLiteral182))) else (if i.val < 620 then (if i.val < 618 then (if i.val < 617 then alphaTargetLiteral181 else alphaTargetLiteral176) else (if i.val < 619 then alphaTargetLiteral183 else alphaTargetLiteral155)) else (if i.val < 622 then (if i.val < 621 then alphaTargetLiteral156 else alphaTargetLiteral182) else (if i.val < 623 then alphaTargetLiteral181 else alphaTargetLiteral171)))) else (if i.val < 632 then (if i.val < 628 then (if i.val < 626 then (if i.val < 625 then alphaTargetLiteral178 else alphaTargetLiteral184) else (if i.val < 627 then alphaTargetLiteral172 else alphaTargetLiteral182)) else (if i.val < 630 then (if i.val < 629 then alphaTargetLiteral181 else alphaTargetLiteral176) else (if i.val < 631 then alphaTargetLiteral183 else alphaTargetLiteral171))) else (if i.val < 636 then (if i.val < 634 then (if i.val < 633 then alphaTargetLiteral178 else alphaTargetLiteral184) else (if i.val < 635 then alphaTargetLiteral166 else alphaTargetLiteral173)) else (if i.val < 638 then (if i.val < 637 then alphaTargetLiteral152 else alphaTargetLiteral180) else (if i.val < 639 then alphaTargetLiteral159 else alphaTargetLiteral145))))))) else (if i.val < 704 then (if i.val < 672 then (if i.val < 656 then (if i.val < 648 then (if i.val < 644 then (if i.val < 642 then (if i.val < 641 then alphaTargetLiteral155 else alphaTargetLiteral156) else (if i.val < 643 then alphaTargetLiteral172 else alphaTargetLiteral182)) else (if i.val < 646 then (if i.val < 645 then alphaTargetLiteral23 else alphaTargetLiteral104) else (if i.val < 647 then alphaTargetLiteral105 else alphaTargetLiteral106))) else (if i.val < 652 then (if i.val < 650 then (if i.val < 649 then alphaTargetLiteral108 else alphaTargetLiteral105) else (if i.val < 651 then alphaTargetLiteral110 else alphaTargetLiteral19)) else (if i.val < 654 then (if i.val < 653 then alphaTargetLiteral90 else alphaTargetLiteral93) else (if i.val < 655 then alphaTargetLiteral94 else alphaTargetLiteral93)))) else (if i.val < 664 then (if i.val < 660 then (if i.val < 658 then (if i.val < 657 then alphaTargetLiteral96 else alphaTargetLiteral83) else (if i.val < 659 then alphaTargetLiteral84 else alphaTargetLiteral86)) else (if i.val < 662 then (if i.val < 661 then alphaTargetLiteral84 else alphaTargetLiteral86) else (if i.val < 663 then alphaTargetLiteral88 else alphaTargetLiteral185))) else (if i.val < 668 then (if i.val < 666 then (if i.val < 665 then alphaTargetLiteral186 else alphaTargetLiteral185) else (if i.val < 667 then alphaTargetLiteral187 else alphaTargetLiteral188)) else (if i.val < 670 then (if i.val < 669 then alphaTargetLiteral185 else alphaTargetLiteral189) else (if i.val < 671 then alphaTargetLiteral190 else alphaTargetLiteral185))))) else (if i.val < 688 then (if i.val < 680 then (if i.val < 676 then (if i.val < 674 then (if i.val < 673 then alphaTargetLiteral187 else alphaTargetLiteral189) else (if i.val < 675 then alphaTargetLiteral191 else alphaTargetLiteral188)) else (if i.val < 678 then (if i.val < 677 then alphaTargetLiteral190 else alphaTargetLiteral192) else (if i.val < 679 then alphaTargetLiteral112 else alphaTargetLiteral98))) else (if i.val < 684 then (if i.val < 682 then (if i.val < 681 then alphaTargetLiteral186 else alphaTargetLiteral193) else (if i.val < 683 then alphaTargetLiteral83 else alphaTargetLiteral192)) else (if i.val < 686 then (if i.val < 685 then alphaTargetLiteral187 else alphaTargetLiteral194) else (if i.val < 687 then alphaTargetLiteral106 else alphaTargetLiteral114)))) else (if i.val < 696 then (if i.val < 692 then (if i.val < 690 then (if i.val < 689 then alphaTargetLiteral193 else alphaTargetLiteral195) else (if i.val < 691 then alphaTargetLiteral83 else alphaTargetLiteral192)) else (if i.val < 694 then (if i.val < 693 then alphaTargetLiteral88 else alphaTargetLiteral101) else (if i.val < 695 then alphaTargetLiteral189 else alphaTargetLiteral196))) else (if i.val < 700 then (if i.val < 698 then (if i.val < 697 then alphaTargetLiteral102 else alphaTargetLiteral193) else (if i.val < 699 then alphaTargetLiteral197 else alphaTargetLiteral192)) else (if i.val < 702 then (if i.val < 701 then alphaTargetLiteral187 else alphaTargetLiteral194) else (if i.val < 703 then alphaTargetLiteral101 else alphaTargetLiteral189)))))) else (if i.val < 736 then (if i.val < 720 then (if i.val < 712 then (if i.val < 708 then (if i.val < 706 then (if i.val < 705 then alphaTargetLiteral196 else alphaTargetLiteral103) else (if i.val < 707 then alphaTargetLiteral191 else alphaTargetLiteral198)) else (if i.val < 710 then (if i.val < 709 then alphaTargetLiteral114 else alphaTargetLiteral117) else (if i.val < 711 then alphaTargetLiteral102 else alphaTargetLiteral193))) else (if i.val < 716 then (if i.val < 714 then (if i.val < 713 then alphaTargetLiteral195 else alphaTargetLiteral197) else (if i.val < 715 then alphaTargetLiteral104 else alphaTargetLiteral108)) else (if i.val < 718 then (if i.val < 717 then alphaTargetLiteral110 else alphaTargetLiteral119) else (if i.val < 719 then alphaTargetLiteral121 else alphaTargetLiteral124)))) else (if i.val < 728 then (if i.val < 724 then (if i.val < 722 then (if i.val < 721 then alphaTargetLiteral121 else alphaTargetLiteral190) else (if i.val < 723 then alphaTargetLiteral191 else alphaTargetLiteral190)) else (if i.val < 726 then (if i.val < 725 then alphaTargetLiteral90 else alphaTargetLiteral94) else (if i.val < 727 then alphaTargetLiteral96 else alphaTargetLiteral98))) else (if i.val < 732 then (if i.val < 730 then (if i.val < 729 then alphaTargetLiteral99 else alphaTargetLiteral99) else (if i.val < 731 then alphaTargetLiteral103 else alphaTargetLiteral199)) else (if i.val < 734 then (if i.val < 733 then alphaTargetLiteral200 else alphaTargetLiteral199) else (if i.val < 735 then alphaTargetLiteral201 else alphaTargetLiteral200))))) else (if i.val < 752 then (if i.val < 744 then (if i.val < 740 then (if i.val < 738 then (if i.val < 737 then alphaTargetLiteral202 else alphaTargetLiteral199) else (if i.val < 739 then alphaTargetLiteral203 else alphaTargetLiteral200)) else (if i.val < 742 then (if i.val < 741 then alphaTargetLiteral204 else alphaTargetLiteral199) else (if i.val < 743 then alphaTargetLiteral201 else alphaTargetLiteral203))) else (if i.val < 748 then (if i.val < 746 then (if i.val < 745 then alphaTargetLiteral205 else alphaTargetLiteral200) else (if i.val < 747 then alphaTargetLiteral202 else alphaTargetLiteral204)) else (if i.val < 750 then (if i.val < 749 then alphaTargetLiteral206 else alphaTargetLiteral112) else (if i.val < 751 then alphaTargetLiteral119 else alphaTargetLiteral207)))) else (if i.val < 760 then (if i.val < 756 then (if i.val < 754 then (if i.val < 753 then alphaTargetLiteral206 else alphaTargetLiteral201) else (if i.val < 755 then alphaTargetLiteral208 else alphaTargetLiteral127)) else (if i.val < 758 then (if i.val < 757 then alphaTargetLiteral128 else alphaTargetLiteral207) else (if i.val < 759 then alphaTargetLiteral206 else alphaTargetLiteral196))) else (if i.val < 764 then (if i.val < 762 then (if i.val < 761 then alphaTargetLiteral203 else alphaTargetLiteral209) else (if i.val < 763 then alphaTargetLiteral197 else alphaTargetLiteral207)) else (if i.val < 766 then (if i.val < 765 then alphaTargetLiteral206 else alphaTargetLiteral201) else (if i.val < 767 then alphaTargetLiteral208 else alphaTargetLiteral196)))))))) else (if i.val < 896 then (if i.val < 832 then (if i.val < 800 then (if i.val < 784 then (if i.val < 776 then (if i.val < 772 then (if i.val < 770 then (if i.val < 769 then alphaTargetLiteral203 else alphaTargetLiteral209) else (if i.val < 771 then alphaTargetLiteral191 else alphaTargetLiteral198)) else (if i.val < 774 then (if i.val < 773 then alphaTargetLiteral124 else alphaTargetLiteral205) else (if i.val < 775 then alphaTargetLiteral131 else alphaTargetLiteral117))) else (if i.val < 780 then (if i.val < 778 then (if i.val < 777 then alphaTargetLiteral127 else alphaTargetLiteral128) else (if i.val < 779 then alphaTargetLiteral197 else alphaTargetLiteral207)) else (if i.val < 782 then (if i.val < 781 then alphaTargetLiteral186 else alphaTargetLiteral188) else (if i.val < 783 then alphaTargetLiteral188 else alphaTargetLiteral123)))) else (if i.val < 792 then (if i.val < 788 then (if i.val < 786 then (if i.val < 785 then alphaTargetLiteral123 else alphaTargetLiteral113) else (if i.val < 787 then alphaTargetLiteral113 else alphaTargetLiteral210)) else (if i.val < 790 then (if i.val < 789 then alphaTargetLiteral211 else alphaTargetLiteral210) else (if i.val < 791 then alphaTargetLiteral212 else alphaTargetLiteral211))) else (if i.val < 796 then (if i.val < 794 then (if i.val < 793 then alphaTargetLiteral213 else alphaTargetLiteral210) else (if i.val < 795 then alphaTargetLiteral214 else alphaTargetLiteral211)) else (if i.val < 798 then (if i.val < 797 then alphaTargetLiteral215 else alphaTargetLiteral210) else (if i.val < 799 then alphaTargetLiteral212 else alphaTargetLiteral214))))) else (if i.val < 816 then (if i.val < 808 then (if i.val < 804 then (if i.val < 802 then (if i.val < 801 then alphaTargetLiteral216 else alphaTargetLiteral211) else (if i.val < 803 then alphaTargetLiteral213 else alphaTargetLiteral215)) else (if i.val < 806 then (if i.val < 805 then alphaTargetLiteral217 else alphaTargetLiteral186) else (if i.val < 807 then alphaTargetLiteral218 else alphaTargetLiteral217))) else (if i.val < 812 then (if i.val < 810 then (if i.val < 809 then alphaTargetLiteral212 else alphaTargetLiteral219) else (if i.val < 811 then alphaTargetLiteral194 else alphaTargetLiteral195)) else (if i.val < 814 then (if i.val < 813 then alphaTargetLiteral218 else alphaTargetLiteral217) else (if i.val < 815 then alphaTargetLiteral129 else alphaTargetLiteral214)))) else (if i.val < 824 then (if i.val < 820 then (if i.val < 818 then (if i.val < 817 then alphaTargetLiteral220 else alphaTargetLiteral130) else (if i.val < 819 then alphaTargetLiteral218 else alphaTargetLiteral217)) else (if i.val < 822 then (if i.val < 821 then alphaTargetLiteral212 else alphaTargetLiteral219) else (if i.val < 823 then alphaTargetLiteral129 else alphaTargetLiteral214))) else (if i.val < 828 then (if i.val < 826 then (if i.val < 825 then alphaTargetLiteral220 else alphaTargetLiteral131) else (if i.val < 827 then alphaTargetLiteral216 else alphaTargetLiteral198)) else (if i.val < 830 then (if i.val < 829 then alphaTargetLiteral194 else alphaTargetLiteral195) else (if i.val < 831 then alphaTargetLiteral130 else alphaTargetLiteral218)))))) else (if i.val < 864 then (if i.val < 848 then (if i.val < 840 then (if i.val < 836 then (if i.val < 834 then (if i.val < 833 then alphaTargetLiteral202 else alphaTargetLiteral205) else (if i.val < 835 then alphaTargetLiteral202 else alphaTargetLiteral215)) else (if i.val < 838 then (if i.val < 837 then alphaTargetLiteral216 else alphaTargetLiteral215) else (if i.val < 839 then alphaTargetLiteral131 else alphaTargetLiteral221))) else (if i.val < 844 then (if i.val < 842 then (if i.val < 841 then alphaTargetLiteral222 else alphaTargetLiteral221) else (if i.val < 843 then alphaTargetLiteral223 else alphaTargetLiteral222)) else (if i.val < 846 then (if i.val < 845 then alphaTargetLiteral221 else alphaTargetLiteral224) else (if i.val < 847 then alphaTargetLiteral222 else alphaTargetLiteral221)))) else (if i.val < 856 then (if i.val < 852 then (if i.val < 850 then (if i.val < 849 then alphaTargetLiteral223 else alphaTargetLiteral224) else (if i.val < 851 then alphaTargetLiteral222 else alphaTargetLiteral225)) else (if i.val < 854 then (if i.val < 853 then alphaTargetLiteral225 else alphaTargetLiteral223) else (if i.val < 855 then alphaTargetLiteral208 else alphaTargetLiteral225))) else (if i.val < 860 then (if i.val < 858 then (if i.val < 857 then alphaTargetLiteral220 else alphaTargetLiteral224) else (if i.val < 859 then alphaTargetLiteral225 else alphaTargetLiteral223)) else (if i.val < 862 then (if i.val < 861 then alphaTargetLiteral208 else alphaTargetLiteral220) else (if i.val < 863 then alphaTargetLiteral224 else alphaTargetLiteral216))))) else (if i.val < 880 then (if i.val < 872 then (if i.val < 868 then (if i.val < 866 then (if i.val < 865 then alphaTargetLiteral198 else alphaTargetLiteral205) else (if i.val < 867 then alphaTargetLiteral161 else alphaTargetLiteral163)) else (if i.val < 870 then (if i.val < 869 then alphaTargetLiteral163 else alphaTargetLiteral151) else (if i.val < 871 then alphaTargetLiteral151 else alphaTargetLiteral141))) else (if i.val < 876 then (if i.val < 874 then (if i.val < 873 then alphaTargetLiteral141 else alphaTargetLiteral226) else (if i.val < 875 then alphaTargetLiteral227 else alphaTargetLiteral226)) else (if i.val < 878 then (if i.val < 877 then alphaTargetLiteral228 else alphaTargetLiteral227) else (if i.val < 879 then alphaTargetLiteral229 else alphaTargetLiteral226)))) else (if i.val < 888 then (if i.val < 884 then (if i.val < 882 then (if i.val < 881 then alphaTargetLiteral230 else alphaTargetLiteral227) else (if i.val < 883 then alphaTargetLiteral231 else alphaTargetLiteral226)) else (if i.val < 886 then (if i.val < 885 then alphaTargetLiteral228 else alphaTargetLiteral230) else (if i.val < 887 then alphaTargetLiteral232 else alphaTargetLiteral227))) else (if i.val < 892 then (if i.val < 890 then (if i.val < 889 then alphaTargetLiteral229 else alphaTargetLiteral231) else (if i.val < 891 then alphaTargetLiteral233 else alphaTargetLiteral161)) else (if i.val < 894 then (if i.val < 893 then alphaTargetLiteral234 else alphaTargetLiteral233) else (if i.val < 895 then alphaTargetLiteral228 else alphaTargetLiteral235))))))) else (if i.val < 960 then (if i.val < 928 then (if i.val < 912 then (if i.val < 904 then (if i.val < 900 then (if i.val < 898 then (if i.val < 897 then alphaTargetLiteral169 else alphaTargetLiteral170) else (if i.val < 899 then alphaTargetLiteral234 else alphaTargetLiteral233)) else (if i.val < 902 then (if i.val < 901 then alphaTargetLiteral157 else alphaTargetLiteral230) else (if i.val < 903 then alphaTargetLiteral236 else alphaTargetLiteral158))) else (if i.val < 908 then (if i.val < 906 then (if i.val < 905 then alphaTargetLiteral234 else alphaTargetLiteral233) else (if i.val < 907 then alphaTargetLiteral228 else alphaTargetLiteral235)) else (if i.val < 910 then (if i.val < 909 then alphaTargetLiteral157 else alphaTargetLiteral230) else (if i.val < 911 then alphaTargetLiteral236 else alphaTargetLiteral159)))) else (if i.val < 920 then (if i.val < 916 then (if i.val < 914 then (if i.val < 913 then alphaTargetLiteral232 else alphaTargetLiteral173) else (if i.val < 915 then alphaTargetLiteral169 else alphaTargetLiteral170)) else (if i.val < 918 then (if i.val < 917 then alphaTargetLiteral158 else alphaTargetLiteral234) else (if i.val < 919 then alphaTargetLiteral177 else alphaTargetLiteral180))) else (if i.val < 924 then (if i.val < 922 then (if i.val < 921 then alphaTargetLiteral177 else alphaTargetLiteral231) else (if i.val < 923 then alphaTargetLiteral232 else alphaTargetLiteral231)) else (if i.val < 926 then (if i.val < 925 then alphaTargetLiteral159 else alphaTargetLiteral237) else (if i.val < 927 then alphaTargetLiteral238 else alphaTargetLiteral237))))) else (if i.val < 944 then (if i.val < 936 then (if i.val < 932 then (if i.val < 930 then (if i.val < 929 then alphaTargetLiteral239 else alphaTargetLiteral238) else (if i.val < 931 then alphaTargetLiteral237 else alphaTargetLiteral240)) else (if i.val < 934 then (if i.val < 933 then alphaTargetLiteral238 else alphaTargetLiteral237) else (if i.val < 935 then alphaTargetLiteral239 else alphaTargetLiteral240))) else (if i.val < 940 then (if i.val < 938 then (if i.val < 937 then alphaTargetLiteral238 else alphaTargetLiteral241) else (if i.val < 939 then alphaTargetLiteral241 else alphaTargetLiteral239)) else (if i.val < 942 then (if i.val < 941 then alphaTargetLiteral183 else alphaTargetLiteral241) else (if i.val < 943 then alphaTargetLiteral236 else alphaTargetLiteral240)))) else (if i.val < 952 then (if i.val < 948 then (if i.val < 946 then (if i.val < 945 then alphaTargetLiteral241 else alphaTargetLiteral239) else (if i.val < 947 then alphaTargetLiteral183 else alphaTargetLiteral236)) else (if i.val < 950 then (if i.val < 949 then alphaTargetLiteral240 else alphaTargetLiteral232) else (if i.val < 951 then alphaTargetLiteral173 else alphaTargetLiteral180))) else (if i.val < 956 then (if i.val < 954 then (if i.val < 953 then alphaTargetLiteral229 else alphaTargetLiteral229) else (if i.val < 955 then alphaTargetLiteral179 else alphaTargetLiteral179)) else (if i.val < 958 then (if i.val < 957 then alphaTargetLiteral242 else alphaTargetLiteral243) else (if i.val < 959 then alphaTargetLiteral242 else alphaTargetLiteral244)))))) else (if i.val < 992 then (if i.val < 976 then (if i.val < 968 then (if i.val < 964 then (if i.val < 962 then (if i.val < 961 then alphaTargetLiteral243 else alphaTargetLiteral242) else (if i.val < 963 then alphaTargetLiteral245 else alphaTargetLiteral243)) else (if i.val < 966 then (if i.val < 965 then alphaTargetLiteral242 else alphaTargetLiteral244) else (if i.val < 967 then alphaTargetLiteral245 else alphaTargetLiteral243))) else (if i.val < 972 then (if i.val < 970 then (if i.val < 969 then alphaTargetLiteral246 else alphaTargetLiteral246) else (if i.val < 971 then alphaTargetLiteral244 else alphaTargetLiteral235)) else (if i.val < 974 then (if i.val < 973 then alphaTargetLiteral246 else alphaTargetLiteral184) else (if i.val < 975 then alphaTargetLiteral245 else alphaTargetLiteral246)))) else (if i.val < 984 then (if i.val < 980 then (if i.val < 978 then (if i.val < 977 then alphaTargetLiteral244 else alphaTargetLiteral235) else (if i.val < 979 then alphaTargetLiteral184 else alphaTargetLiteral245)) else (if i.val < 982 then (if i.val < 981 then alphaTargetLiteral247 else alphaTargetLiteral247) else (if i.val < 983 then alphaTargetLiteral247 else alphaTargetLiteral247))) else (if i.val < 988 then (if i.val < 986 then (if i.val < 985 then alphaTargetLiteral213 else alphaTargetLiteral213) else (if i.val < 987 then alphaTargetLiteral204 else alphaTargetLiteral204)) else (if i.val < 990 then (if i.val < 989 then alphaTargetLiteral248 else alphaTargetLiteral249) else (if i.val < 991 then alphaTargetLiteral248 else alphaTargetLiteral250))))) else (if i.val < 1008 then (if i.val < 1000 then (if i.val < 996 then (if i.val < 994 then (if i.val < 993 then alphaTargetLiteral249 else alphaTargetLiteral248) else (if i.val < 995 then alphaTargetLiteral251 else alphaTargetLiteral249)) else (if i.val < 998 then (if i.val < 997 then alphaTargetLiteral248 else alphaTargetLiteral250) else (if i.val < 999 then alphaTargetLiteral251 else alphaTargetLiteral249))) else (if i.val < 1004 then (if i.val < 1002 then (if i.val < 1001 then alphaTargetLiteral252 else alphaTargetLiteral252) else (if i.val < 1003 then alphaTargetLiteral250 else alphaTargetLiteral219)) else (if i.val < 1006 then (if i.val < 1005 then alphaTargetLiteral252 else alphaTargetLiteral209) else (if i.val < 1007 then alphaTargetLiteral251 else alphaTargetLiteral252)))) else (if i.val < 1016 then (if i.val < 1012 then (if i.val < 1010 then (if i.val < 1009 then alphaTargetLiteral250 else alphaTargetLiteral219) else (if i.val < 1011 then alphaTargetLiteral209 else alphaTargetLiteral251)) else (if i.val < 1014 then (if i.val < 1013 then alphaTargetLiteral253 else alphaTargetLiteral253) else (if i.val < 1015 then alphaTargetLiteral253 else alphaTargetLiteral253))) else (if i.val < 1020 then (if i.val < 1018 then (if i.val < 1017 then alphaTargetLiteral254 else alphaTargetLiteral254) else (if i.val < 1019 then alphaTargetLiteral254 else alphaTargetLiteral254)) else (if i.val < 1022 then (if i.val < 1021 then alphaTargetLiteral255 else alphaTargetLiteral255) else (if i.val < 1023 then alphaTargetLiteral255 else alphaTargetLiteral255))))))))))

def alphaGenerators (j : Fin 4) := alphaSource (#[1,2,3,4][j.val]!)
def alphaImages (j : Fin 4) := alphaTarget (#[1,2,3,4][j.val]!)
private def alphaNextTable (i : Fin 1024) : Array (Fin 1024) :=
  (if i.val < 512 then (if i.val < 256 then (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3,4] else #[0,5,6,7]) else (if i.val < 3 then #[5,0,8,9] else #[10,11,12,13])) else (if i.val < 6 then (if i.val < 5 then #[14,15,16,17] else #[2,1,18,19]) else (if i.val < 7 then #[20,21,22,23] else #[24,25,26,27]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[28,29,30,31] else #[32,33,34,35]) else (if i.val < 11 then #[3,36,37,38] else #[36,3,39,40])) else (if i.val < 14 then (if i.val < 13 then #[22,30,41,42] else #[43,44,45,46]) else (if i.val < 15 then #[4,47,48,49] else #[47,4,50,51])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[52,53,42,54] else #[55,56,46,57]) else (if i.val < 19 then #[58,59,60,61] else #[62,63,64,65])) else (if i.val < 22 then (if i.val < 21 then #[6,66,67,68] else #[66,6,69,70]) else (if i.val < 23 then #[12,60,71,72] else #[73,74,75,76]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[7,77,78,79] else #[77,7,80,81]) else (if i.val < 27 then #[82,83,72,84] else #[85,86,76,87])) else (if i.val < 30 then (if i.val < 29 then #[8,71,88,89] else #[71,8,90,91]) else (if i.val < 31 then #[60,12,66,92] else #[93,94,95,96]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[9,97,98,99] else #[97,9,100,101]) else (if i.val < 35 then #[102,103,92,104] else #[105,106,96,107])) else (if i.val < 38 then (if i.val < 37 then #[11,10,5,108] else #[67,88,59,109]) else (if i.val < 39 then #[110,111,112,113] else #[69,90,58,114]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[115,116,117,118] else #[59,58,0,119]) else (if i.val < 43 then #[120,121,122,123] else #[13,124,125,126])) else (if i.val < 46 then (if i.val < 45 then #[124,13,127,128] else #[129,130,119,131]) else (if i.val < 47 then #[76,96,123,132] else #[15,14,133,134])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[135,136,120,137] else #[138,139,140,141]) else (if i.val < 51 then #[142,143,121,144] else #[145,146,128,147])) else (if i.val < 54 then (if i.val < 53 then #[16,148,149,150] else #[148,16,151,152]) else (if i.val < 55 then #[84,153,154,155] else #[17,156,113,157]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[156,17,118,158] else #[159,160,155,12]) else (if i.val < 59 then #[18,41,161,162] else #[41,18,163,164])) else (if i.val < 62 then (if i.val < 61 then #[30,22,36,165] else #[166,167,168,169]) else (if i.val < 63 then #[19,170,171,172] else #[170,19,173,174])))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then #[175,176,165,177] else #[178,179,169,180]) else (if i.val < 67 then #[21,20,2,181] else #[37,161,29,182])) else (if i.val < 70 then (if i.val < 69 then #[183,184,185,186] else #[39,163,28,187]) else (if i.val < 71 then #[188,189,190,191] else #[29,28,1,192]))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then #[193,194,195,196] else #[23,197,198,199]) else (if i.val < 75 then #[197,23,200,201] else #[202,203,192,204])) else (if i.val < 78 then (if i.val < 77 then #[46,169,196,205] else #[25,24,206,207]) else (if i.val < 79 then #[208,209,193,210] else #[211,212,213,214])))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then #[215,216,194,217] else #[218,219,201,220]) else (if i.val < 83 then #[26,221,222,223] else #[221,26,224,225])) else (if i.val < 86 then (if i.val < 85 then #[54,226,227,228] else #[27,229,186,230]) else (if i.val < 87 then #[229,27,191,231] else #[232,233,228,22]))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then #[161,37,21,234] else #[235,236,237,238]) else (if i.val < 91 then #[163,39,20,239] else #[240,241,242,243])) else (if i.val < 94 then (if i.val < 93 then #[244,245,246,229] else #[31,247,248,249]) else (if i.val < 95 then #[247,31,250,251] else #[252,253,181,254]))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then #[169,46,229,255] else #[33,32,256,257]) else (if i.val < 99 then #[258,259,244,260] else #[261,262,263,264])) else (if i.val < 102 then (if i.val < 101 then #[265,266,245,267] else #[268,269,251,270]) else (if i.val < 103 then #[34,271,272,273] else #[271,34,274,275]))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then #[177,276,277,278] else #[35,196,238,279]) else (if i.val < 107 then #[196,35,243,280] else #[281,282,278,30])) else (if i.val < 110 then (if i.val < 109 then #[283,284,285,286] else #[287,224,208,179]) else (if i.val < 111 then #[38,288,289,290] else #[288,38,203,291])))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then #[292,200,164,293] else #[186,238,179,294]) else (if i.val < 115 then #[272,295,266,178] else #[40,296,252,263])) else (if i.val < 118 then (if i.val < 117 then #[296,40,297,298] else #[248,299,162,300]) else (if i.val < 119 then #[191,243,178,301] else #[302,303,304,305]))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then #[42,306,307,308] else #[306,42,309,310]) else (if i.val < 123 then #[311,312,4,313] else #[179,178,305,314])) else (if i.val < 126 then (if i.val < 125 then #[44,43,315,316] else #[242,317,302,318]) else (if i.val < 127 then #[199,249,211,319] else #[320,185,303,321]))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then #[201,251,310,322] else #[45,323,183,324]) else (if i.val < 131 then #[323,45,241,325] else #[293,254,54,326])) else (if i.val < 134 then (if i.val < 133 then #[327,328,326,41] else #[312,311,306,329]) else (if i.val < 135 then #[330,331,332,333] else #[48,309,239,276]))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then #[309,48,334,335] else #[210,273,336,337]) else (if i.val < 139 then #[49,338,339,340] else #[338,49,249,281])) else (if i.val < 142 then (if i.val < 141 then #[213,263,308,327] else #[280,341,337,342]) else (if i.val < 143 then #[50,307,343,344] else #[307,50,182,345])))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then #[217,346,347,348] else #[51,349,291,233]) else (if i.val < 147 then #[349,51,298,350] else #[351,230,348,352])) else (if i.val < 150 then (if i.val < 149 then #[53,52,47,353] else #[239,343,311,211]) else (if i.val < 151 then #[223,260,354,355] else #[334,182,312,269]))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then #[225,356,357,358] else #[226,54,359,360]) else (if i.val < 155 then #[361,277,313,362] else #[337,348,314,363])) else (if i.val < 158 then (if i.val < 157 then #[56,55,286,364] else #[365,220,366,37]) else (if i.val < 159 then #[264,367,360,39] else #[57,368,355,369]))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then #[368,57,358,370] else #[88,67,11,371]) else (if i.val < 163 then #[372,373,374,375] else #[90,69,10,376])) else (if i.val < 166 then (if i.val < 165 then #[377,378,379,380] else #[381,382,383,156]) else (if i.val < 167 then #[61,384,385,386] else #[384,61,387,388]))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then #[389,390,108,391] else #[96,76,156,392]) else (if i.val < 171 then #[63,62,393,394] else #[395,396,381,397])) else (if i.val < 174 then (if i.val < 173 then #[398,399,400,401] else #[402,403,382,404]) else (if i.val < 175 then #[405,406,388,407] else #[64,408,409,410])))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then #[408,64,411,412] else #[104,413,414,415]) else (if i.val < 179 then #[65,123,375,416] else #[123,65,380,417])) else (if i.val < 182 then (if i.val < 181 then #[418,419,415,60] else #[420,421,422,423]) else (if i.val < 183 then #[424,151,135,106] else #[68,425,426,427]))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then #[425,68,130,428] else #[429,127,91,430]) else (if i.val < 187 then #[113,375,106,431] else #[409,432,403,105])) else (if i.val < 190 then (if i.val < 189 then #[70,433,389,400] else #[433,70,434,435]) else (if i.val < 191 then #[385,436,89,437] else #[118,380,105,438])))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then #[439,440,441,442] else #[72,443,444,445]) else (if i.val < 195 then #[443,72,446,447] else #[448,449,7,450])) else (if i.val < 198 then (if i.val < 197 then #[106,105,442,451] else #[74,73,452,453]) else (if i.val < 199 then #[379,454,439,455] else #[126,386,138,456]))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then #[457,112,440,458] else #[128,388,447,459]) else (if i.val < 203 then #[75,460,110,461] else #[460,75,378,462])) else (if i.val < 206 then (if i.val < 205 then #[430,391,84,463] else #[464,465,463,71]) else (if i.val < 207 then #[449,448,443,466] else #[467,468,469,470])))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then #[78,446,376,413] else #[446,78,471,472]) else (if i.val < 211 then #[137,410,473,474] else #[79,475,476,477])) else (if i.val < 214 then (if i.val < 213 then #[475,79,386,418] else #[140,400,445,464]) else (if i.val < 215 then #[417,478,474,479] else #[80,444,480,481]))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then #[444,80,109,482] else #[144,483,484,485]) else (if i.val < 219 then #[81,486,428,160] else #[486,81,435,487])) else (if i.val < 222 then (if i.val < 221 then #[488,157,485,489] else #[83,82,77,490]) else (if i.val < 223 then #[376,480,448,138] else #[150,397,491,492]))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then #[471,109,449,406] else #[152,493,494,495]) else (if i.val < 227 then #[153,84,496,497] else #[498,414,450,499])) else (if i.val < 230 then (if i.val < 229 then #[474,485,451,500] else #[86,85,423,501]) else (if i.val < 231 then #[502,147,503,67] else #[401,504,497,69]))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then #[87,505,492,506] else #[505,87,495,507]) else (if i.val < 235 then #[508,411,395,86] else #[89,509,510,511])) else (if i.val < 238 then (if i.val < 237 then #[509,89,390,512] else #[513,387,70,496]) else (if i.val < 239 then #[375,113,86,514] else #[149,515,143,85])))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then #[91,516,129,140] else #[516,91,517,518]) else (if i.val < 243 then #[125,519,68,498] else #[380,118,85,520])) else (if i.val < 246 then (if i.val < 245 then #[92,521,522,475] else #[521,92,523,486]) else (if i.val < 247 then #[524,525,9,526] else #[94,93,527,528]))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then #[117,529,420,530] else #[386,126,398,531]) else (if i.val < 251 then #[532,374,421,533] else #[388,128,486,534])) else (if i.val < 254 then (if i.val < 253 then #[95,535,372,536] else #[535,95,116,537]) else (if i.val < 255 then #[496,131,104,538] else #[539,540,538,66])))))))) else (if i.val < 384 then (if i.val < 320 then (if i.val < 288 then (if i.val < 272 then (if i.val < 264 then (if i.val < 260 then (if i.val < 258 then (if i.val < 257 then #[525,524,521,541] else #[542,543,544,545]) else (if i.val < 259 then #[98,523,114,153] else #[523,98,546,547])) else (if i.val < 262 then (if i.val < 261 then #[397,150,548,549] else #[99,445,550,551]) else (if i.val < 263 then #[445,99,126,159] else #[400,140,475,539]))) else (if i.val < 268 then (if i.val < 266 then (if i.val < 265 then #[158,552,549,553] else #[100,522,554,555]) else (if i.val < 267 then #[522,100,371,556] else #[404,557,558,559])) else (if i.val < 270 then (if i.val < 269 then #[101,447,512,419] else #[447,101,518,560]) else (if i.val < 271 then #[561,416,559,562] else #[103,102,97,563])))) else (if i.val < 280 then (if i.val < 276 then (if i.val < 274 then (if i.val < 273 then #[114,554,524,398] else #[410,137,564,565]) else (if i.val < 275 then #[546,371,525,146] else #[412,566,567,568])) else (if i.val < 278 then (if i.val < 277 then #[413,104,430,569] else #[437,154,526,570]) else (if i.val < 279 then #[549,559,501,571] else #[572,407,573,88]))) else (if i.val < 284 then (if i.val < 282 then (if i.val < 281 then #[141,574,569,90] else #[107,575,565,576]) else (if i.val < 283 then #[575,107,568,577] else #[108,578,513,550])) else (if i.val < 286 then (if i.val < 285 then #[578,108,436,579] else #[510,434,61,414]) else (if i.val < 287 then #[423,442,65,580] else #[109,471,82,399]))))) else (if i.val < 304 then (if i.val < 296 then (if i.val < 292 then (if i.val < 290 then (if i.val < 289 then #[111,110,454,581] else #[441,452,377,473]) else (if i.val < 291 then #[427,511,79,582] else #[428,512,406,465])) else (if i.val < 294 then (if i.val < 293 then #[112,457,73,491] else #[131,496,482,583]) else (if i.val < 295 then #[584,459,583,59] else #[554,114,103,405]))) else (if i.val < 300 then (if i.val < 298 then (if i.val < 297 then #[116,115,532,544] else #[527,422,373,567]) else (if i.val < 299 then #[435,518,405,585] else #[529,117,94,558])) else (if i.val < 302 then (if i.val < 301 then #[414,498,153,586] else #[531,587,586,58]) else (if i.val < 303 then #[119,588,429,476] else #[588,119,519,589])))) else (if i.val < 312 then (if i.val < 308 then (if i.val < 306 then (if i.val < 305 then #[426,517,13,154] else #[442,423,17,590]) else (if i.val < 307 then #[121,120,148,591] else #[143,142,14,592])) else (if i.val < 310 then (if i.val < 309 then #[399,398,427,502] else #[136,135,15,566]) else (if i.val < 311 then #[406,405,589,574] else #[122,133,424,593]))) else (if i.val < 316 then (if i.val < 314 then (if i.val < 313 then #[133,122,515,557] else #[450,556,131,594]) else (if i.val < 315 then #[477,560,594,0] else #[517,426,588,595])) else (if i.val < 318 then (if i.val < 317 then #[453,528,467,596] else #[519,125,516,597]) else (if i.val < 319 then #[473,530,150,598] else #[520,599,598,600])))))) else (if i.val < 352 then (if i.val < 336 then (if i.val < 328 then (if i.val < 324 then (if i.val < 322 then (if i.val < 321 then #[127,429,425,601] else #[462,533,144,602]) else (if i.val < 323 then #[603,431,602,604] else #[130,129,124,605])) else (if i.val < 326 then (if i.val < 325 then #[491,536,137,606] else #[458,537,152,607]) else (if i.val < 327 then #[598,602,590,608] else #[132,609,606,610]))) else (if i.val < 332 then (if i.val < 330 then (if i.val < 329 then #[609,132,607,611] else #[466,555,597,612]) else (if i.val < 331 then #[134,613,614,478] else #[613,134,528,561])) else (if i.val < 334 then (if i.val < 333 then #[469,544,591,603] else #[560,477,612,615]) else (if i.val < 335 then #[151,424,142,543] else #[472,563,595,616])))) else (if i.val < 344 then (if i.val < 340 then (if i.val < 338 then (if i.val < 337 then #[455,548,592,617] else #[155,612,502,618]) else (if i.val < 339 then #[139,138,511,572] else #[476,550,399,584])) else (if i.val < 342 then (if i.val < 341 then #[451,470,619,620] else #[574,141,616,621]) else (if i.val < 343 then #[479,553,610,120] else #[515,149,136,467]))) else (if i.val < 348 then (if i.val < 346 then (if i.val < 345 then #[481,541,605,622] else #[482,526,498,503]) else (if i.val < 347 then #[483,144,537,623] else #[494,558,566,624])) else (if i.val < 350 then (if i.val < 349 then #[612,155,574,625] else #[146,145,579,504]) else (if i.val < 351 then #[545,501,623,626] else #[147,502,622,627]))))) else (if i.val < 368 then (if i.val < 360 then (if i.val < 356 then (if i.val < 354 then (if i.val < 353 then #[489,562,604,121] else #[490,547,601,628]) else (if i.val < 355 then #[461,564,593,629] else #[569,622,477,630])) else (if i.val < 358 then (if i.val < 357 then #[493,152,533,631] else #[484,567,557,632]) else (if i.val < 359 then #[616,503,560,633] else #[391,430,556,634]))) else (if i.val < 364 then (if i.val < 362 then (if i.val < 361 then #[565,623,416,635] else #[154,437,413,636]) else (if i.val < 363 then #[629,624,132,637] else #[638,571,637,122])) else (if i.val < 366 then (if i.val < 365 then #[551,487,639,5] else #[157,488,640,641]) else (if i.val < 367 then #[619,495,417,638] else #[552,158,631,642])))) else (if i.val < 376 then (if i.val < 372 then (if i.val < 370 then (if i.val < 369 then #[160,159,628,643] else #[506,576,600,149]) else (if i.val < 371 then #[507,577,611,151] else #[644,274,258,56])) else (if i.val < 374 then (if i.val < 373 then #[162,645,646,647] else #[645,162,253,648]) else (if i.val < 375 then #[649,250,40,359] else #[238,186,56,650]))) else (if i.val < 380 then (if i.val < 378 then (if i.val < 377 then #[222,651,216,55] else #[164,652,202,213]) else (if i.val < 379 then #[652,164,653,654] else #[198,655,38,361])) else (if i.val < 382 then (if i.val < 381 then #[243,191,55,656] else #[165,657,658,338]) else (if i.val < 383 then #[657,165,659,349] else #[660,661,19,662]))))))) else (if i.val < 448 then (if i.val < 416 then (if i.val < 400 then (if i.val < 392 then (if i.val < 388 then (if i.val < 386 then (if i.val < 385 then #[167,166,663,664] else #[190,665,283,666]) else (if i.val < 387 then #[249,199,261,667] else #[668,237,284,669])) else (if i.val < 390 then (if i.val < 389 then #[251,201,349,670] else #[168,671,235,672]) else (if i.val < 391 then #[671,168,189,673] else #[359,204,177,674]))) else (if i.val < 396 then (if i.val < 394 then (if i.val < 393 then #[675,676,674,36] else #[661,660,657,677]) else (if i.val < 395 then #[678,679,680,681] else #[171,659,187,226])) else (if i.val < 398 then (if i.val < 397 then #[659,171,682,683] else #[260,223,684,685]) else (if i.val < 399 then #[172,308,686,687] else #[308,172,199,232])))) else (if i.val < 408 then (if i.val < 404 then (if i.val < 402 then (if i.val < 401 then #[263,213,338,675] else #[231,688,685,689]) else (if i.val < 403 then #[173,658,690,691] else #[658,173,234,692])) else (if i.val < 406 then (if i.val < 405 then #[267,693,694,695] else #[174,310,648,282]) else (if i.val < 407 then #[310,174,654,696] else #[697,279,695,698]))) else (if i.val < 412 then (if i.val < 410 then (if i.val < 409 then #[176,175,170,699] else #[187,690,660,261]) else (if i.val < 411 then #[273,210,700,701] else #[682,234,661,219])) else (if i.val < 414 then (if i.val < 413 then #[275,702,703,704] else #[276,177,293,705]) else (if i.val < 415 then #[300,227,662,706] else #[685,695,364,707]))))) else (if i.val < 432 then (if i.val < 424 then (if i.val < 420 then (if i.val < 418 then (if i.val < 417 then #[708,270,709,161] else #[214,710,705,163]) else (if i.val < 419 then #[180,711,701,712] else #[711,180,704,713])) else (if i.val < 422 then (if i.val < 421 then #[181,714,649,686] else #[714,181,299,715]) else (if i.val < 423 then #[646,297,31,277] else #[286,305,35,716]))) else (if i.val < 428 then (if i.val < 426 then (if i.val < 425 then #[182,334,52,262] else #[184,183,317,717]) else (if i.val < 427 then #[304,315,240,336] else #[290,647,49,718])) else (if i.val < 430 then (if i.val < 429 then #[291,648,269,328] else #[185,320,43,354]) else (if i.val < 431 then #[204,359,345,719] else #[720,322,719,29])))) else (if i.val < 440 then (if i.val < 436 then (if i.val < 434 then (if i.val < 433 then #[690,187,176,268] else #[189,188,668,680]) else (if i.val < 435 then #[663,285,236,703] else #[298,654,268,721])) else (if i.val < 438 then (if i.val < 437 then #[665,190,167,694] else #[277,361,226,722]) else (if i.val < 439 then #[667,723,722,28] else #[192,724,292,339]))) else (if i.val < 444 then (if i.val < 442 then (if i.val < 441 then #[724,192,655,725] else #[289,653,23,227]) else (if i.val < 443 then #[305,286,27,726] else #[194,193,221,727])) else (if i.val < 446 then (if i.val < 445 then #[216,215,24,728] else #[262,261,290,365]) else (if i.val < 447 then #[209,208,25,702] else #[269,268,725,710])))))) else (if i.val < 480 then (if i.val < 464 then (if i.val < 456 then (if i.val < 452 then (if i.val < 450 then (if i.val < 449 then #[195,206,287,729] else #[206,195,651,693]) else (if i.val < 451 then #[313,692,204,730] else #[340,696,730,1])) else (if i.val < 454 then (if i.val < 453 then #[653,289,724,731] else #[316,664,330,732]) else (if i.val < 455 then #[655,198,652,733] else #[336,666,223,734]))) else (if i.val < 460 then (if i.val < 458 then (if i.val < 457 then #[656,735,734,736] else #[200,292,288,737]) else (if i.val < 459 then #[325,669,217,738] else #[739,294,738,740])) else (if i.val < 462 then (if i.val < 461 then #[203,202,197,741] else #[354,672,210,742]) else (if i.val < 463 then #[321,673,225,743] else #[734,738,726,744])))) else (if i.val < 472 then (if i.val < 468 then (if i.val < 466 then (if i.val < 465 then #[205,745,742,746] else #[745,205,743,747]) else (if i.val < 467 then #[329,691,733,748] else #[207,749,750,341])) else (if i.val < 470 then (if i.val < 469 then #[749,207,664,697] else #[332,680,727,739]) else (if i.val < 471 then #[696,340,748,751] else #[224,287,215,679]))) else (if i.val < 476 then (if i.val < 474 then (if i.val < 473 then #[335,699,731,752] else #[318,684,728,753]) else (if i.val < 475 then #[228,748,365,754] else #[212,211,647,708])) else (if i.val < 478 then (if i.val < 477 then #[339,686,262,720] else #[314,333,755,756]) else (if i.val < 479 then #[710,214,752,757] else #[342,689,746,193]))))) else (if i.val < 496 then (if i.val < 488 then (if i.val < 484 then (if i.val < 482 then (if i.val < 481 then #[651,222,209,330] else #[344,677,741,758]) else (if i.val < 483 then #[345,662,361,366] else #[346,217,673,759])) else (if i.val < 486 then (if i.val < 485 then #[357,694,702,760] else #[748,228,710,761]) else (if i.val < 487 then #[219,218,715,367] else #[681,364,759,762]))) else (if i.val < 492 then (if i.val < 490 then (if i.val < 489 then #[220,365,758,763] else #[352,698,740,194]) else (if i.val < 491 then #[353,683,737,764] else #[324,700,729,765])) else (if i.val < 494 then (if i.val < 493 then #[705,758,340,766] else #[356,225,669,767]) else (if i.val < 495 then #[347,703,693,768] else #[752,366,696,769])))) else (if i.val < 504 then (if i.val < 500 then (if i.val < 498 then (if i.val < 497 then #[254,293,692,770] else #[701,759,279,771]) else (if i.val < 499 then #[227,300,276,772] else #[765,760,205,773])) else (if i.val < 502 then (if i.val < 501 then #[774,707,773,195] else #[687,350,775,2]) else (if i.val < 503 then #[230,351,776,777] else #[755,358,280,774]))) else (if i.val < 508 then (if i.val < 506 then (if i.val < 505 then #[688,231,767,778] else #[233,232,764,779]) else (if i.val < 507 then #[369,712,736,222] else #[370,713,747,224])) else (if i.val < 510 then (if i.val < 509 then #[234,682,175,212] else #[236,235,665,780]) else (if i.val < 511 then #[285,663,188,684] else #[647,290,172,781]))))))))) else (if i.val < 768 then (if i.val < 640 then (if i.val < 576 then (if i.val < 544 then (if i.val < 528 then (if i.val < 520 then (if i.val < 516 then (if i.val < 514 then (if i.val < 513 then #[648,291,219,676] else #[237,668,166,700]) else (if i.val < 515 then #[782,670,770,21] else #[343,239,53,218])) else (if i.val < 518 then (if i.val < 517 then #[241,240,320,332] else #[315,304,184,357]) else (if i.val < 519 then #[654,298,218,783] else #[317,242,44,347]))) else (if i.val < 524 then (if i.val < 522 then (if i.val < 521 then #[319,784,772,20] else #[245,244,271,749]) else (if i.val < 523 then #[266,265,32,785] else #[259,258,33,356])) else (if i.val < 526 then (if i.val < 525 then #[246,256,644,786] else #[256,246,295,346]) else (if i.val < 527 then #[662,345,254,775] else #[297,646,714,787])))) else (if i.val < 536 then (if i.val < 532 then (if i.val < 530 then (if i.val < 529 then #[664,316,678,788] else #[299,248,296,789]) else (if i.val < 531 then #[684,318,273,790] else #[301,791,790,792])) else (if i.val < 534 then (if i.val < 533 then #[250,649,645,793] else #[673,321,267,794]) else (if i.val < 535 then #[795,650,794,796] else #[253,252,247,797]))) else (if i.val < 540 then (if i.val < 538 then (if i.val < 537 then #[700,324,260,798] else #[669,325,275,799]) else (if i.val < 539 then #[790,794,716,800] else #[255,801,798,802])) else (if i.val < 542 then (if i.val < 541 then #[801,255,799,803] else #[677,344,789,804]) else (if i.val < 543 then #[257,727,805,688] else #[727,257,316,351]))))) else (if i.val < 560 then (if i.val < 552 then (if i.val < 548 then (if i.val < 546 then (if i.val < 545 then #[680,332,749,795] else #[350,687,804,806]) else (if i.val < 547 then #[274,644,265,331] else #[683,353,787,807])) else (if i.val < 550 then (if i.val < 549 then #[666,336,785,808] else #[278,804,708,809]) else (if i.val < 551 then #[686,339,212,782] else #[364,681,810,811]))) else (if i.val < 556 then (if i.val < 554 then (if i.val < 553 then #[367,264,807,812] else #[689,342,802,244]) else (if i.val < 555 then #[295,272,259,678] else #[691,329,797,813])) else (if i.val < 558 then (if i.val < 557 then #[692,313,300,709] else #[693,267,325,814]) else (if i.val < 559 then #[703,347,356,815] else #[804,278,367,816])))) else (if i.val < 568 then (if i.val < 564 then (if i.val < 562 then (if i.val < 561 then #[333,314,814,817] else #[270,708,813,818]) else (if i.val < 563 then #[698,352,796,245] else #[699,335,793,819])) else (if i.val < 566 then (if i.val < 565 then #[672,354,786,820] else #[360,813,687,821]) else (if i.val < 567 then #[702,275,321,822] else #[694,357,346,823]))) else (if i.val < 572 then (if i.val < 570 then (if i.val < 569 then #[807,709,350,824] else #[355,814,230,825]) else (if i.val < 571 then #[820,815,255,826] else #[827,363,826,246])) else (if i.val < 574 then (if i.val < 573 then #[279,697,828,829] else #[810,704,231,827]) else (if i.val < 575 then #[341,280,822,830] else #[282,281,819,831])))))) else (if i.val < 608 then (if i.val < 592 then (if i.val < 584 then (if i.val < 580 then (if i.val < 578 then (if i.val < 577 then #[712,369,792,272] else #[713,370,803,274]) else (if i.val < 579 then #[284,283,671,805] else #[715,725,174,723])) else (if i.val < 582 then (if i.val < 581 then #[781,721,706,18] else #[717,780,207,735]) else (if i.val < 583 then #[726,732,753,832] else #[753,743,656,833]))) else (if i.val < 588 then (if i.val < 586 then (if i.val < 585 then #[294,739,765,834] else #[788,716,823,835]) else (if i.val < 587 then #[798,823,650,836] else #[791,301,815,837])) else (if i.val < 590 then (if i.val < 589 then #[303,302,323,750] else #[725,715,51,784]) else (if i.val < 591 then #[718,783,362,3] else #[679,678,717,368])))) else (if i.val < 600 then (if i.val < 596 then (if i.val < 594 then (if i.val < 593 then #[728,786,324,776] else #[729,785,318,755]) else (if i.val < 595 then #[776,822,57,838] else #[733,787,344,839])) else (if i.val < 598 then (if i.val < 597 then #[783,718,839,840] else #[731,789,353,841]) else (if i.val < 599 then #[326,839,720,842] else #[784,319,841,843]))) else (if i.val < 604 then (if i.val < 602 then (if i.val < 601 then #[832,802,756,302] else #[741,793,329,844]) else (if i.val < 603 then #[839,326,784,845] else #[322,720,844,846])) else (if i.val < 606 then (if i.val < 605 then #[747,835,830,303] else #[737,797,335,847]) else (if i.val < 607 then #[772,844,718,848] else #[841,719,783,849]))))) else (if i.val < 624 then (if i.val < 616 then (if i.val < 612 then (if i.val < 610 then (if i.val < 609 then #[744,836,363,304] else #[328,327,847,850]) else (if i.val < 611 then #[834,792,777,183] else #[740,837,817,241])) else (if i.val < 614 then (if i.val < 613 then #[348,337,368,851] else #[331,330,780,711]) else (if i.val < 615 then #[750,805,679,745] else #[751,806,846,306]))) else (if i.val < 620 then (if i.val < 618 then (if i.val < 617 then #[358,755,351,852] else #[719,841,327,853]) else (if i.val < 619 then #[854,809,853,307] else #[366,752,232,854])) else (if i.val < 622 then (if i.val < 621 then #[756,811,834,287] else #[757,812,850,334]) else (if i.val < 623 then #[814,355,341,855] else #[813,360,282,856])))) else (if i.val < 632 then (if i.val < 628 then (if i.val < 626 then (if i.val < 625 then #[847,362,322,857] else #[769,816,857,309]) else (if i.val < 627 then #[762,817,835,295] else #[763,818,840,343])) else (if i.val < 630 then (if i.val < 629 then #[822,776,333,858] else #[362,847,319,859]) else (if i.val < 631 then #[860,821,859,311] else #[819,775,270,861]))) else (if i.val < 636 then (if i.val < 634 then (if i.val < 633 then #[844,772,328,862] else #[761,824,862,312]) else (if i.val < 635 then #[808,799,301,863] else #[864,825,863,266])) else (if i.val < 638 then (if i.val < 637 then #[742,768,294,865] else #[773,863,838,45]) else (if i.val < 639 then #[363,827,865,208] else #[828,767,180,864]))))))) else (if i.val < 704 then (if i.val < 672 then (if i.val < 656 then (if i.val < 648 then (if i.val < 644 then (if i.val < 642 then (if i.val < 641 then #[730,764,214,860] else #[777,829,832,24]) else (if i.val < 643 then #[778,830,837,33] else #[779,831,843,47])) else (if i.val < 646 then (if i.val < 645 then #[371,546,102,139] else #[373,372,529,866]) else (if i.val < 647 then #[422,527,115,548] else #[511,427,99,867]))) else (if i.val < 652 then (if i.val < 650 then (if i.val < 649 then #[512,428,146,540] else #[374,532,93,564]) else (if i.val < 651 then #[868,534,634,11] else #[480,376,83,145])) else (if i.val < 654 then (if i.val < 653 then #[378,377,457,469] else #[452,441,111,494]) else (if i.val < 655 then #[518,435,145,869] else #[454,379,74,484])))) else (if i.val < 664 then (if i.val < 660 then (if i.val < 658 then (if i.val < 657 then #[456,870,636,10] else #[382,381,408,613]) else (if i.val < 659 then #[403,402,62,871] else #[396,395,63,493])) else (if i.val < 662 then (if i.val < 661 then #[383,393,508,872] else #[393,383,432,483]) else (if i.val < 663 then #[526,482,391,639] else #[434,510,578,873]))) else (if i.val < 668 then (if i.val < 666 then (if i.val < 665 then #[528,453,542,874] else #[436,385,433,875]) else (if i.val < 667 then #[548,455,410,876] else #[438,877,876,878])) else (if i.val < 670 then (if i.val < 669 then #[387,513,509,879] else #[537,458,404,880]) else (if i.val < 671 then #[881,514,880,882] else #[390,389,384,883]))))) else (if i.val < 688 then (if i.val < 680 then (if i.val < 676 then (if i.val < 674 then (if i.val < 673 then #[564,461,397,884] else #[533,462,412,885]) else (if i.val < 675 then #[876,880,580,886] else #[392,887,884,888])) else (if i.val < 678 then (if i.val < 677 then #[887,392,885,889] else #[541,481,875,890]) else (if i.val < 679 then #[394,591,891,552] else #[591,394,453,488]))) else (if i.val < 684 then (if i.val < 682 then (if i.val < 681 then #[544,469,613,881] else #[487,551,890,892]) else (if i.val < 683 then #[411,508,402,468] else #[547,490,873,893])) else (if i.val < 686 then (if i.val < 685 then #[530,473,871,894] else #[415,890,572,895]) else (if i.val < 687 then #[550,476,139,868] else #[501,545,896,897])))) else (if i.val < 696 then (if i.val < 692 then (if i.val < 690 then (if i.val < 689 then #[504,401,893,898] else #[553,479,888,381]) else (if i.val < 691 then #[432,409,396,542] else #[555,466,883,899])) else (if i.val < 694 then (if i.val < 693 then #[556,450,437,573] else #[557,404,462,900]) else (if i.val < 695 then #[567,484,493,901] else #[890,415,504,902]))) else (if i.val < 700 then (if i.val < 698 then (if i.val < 697 then #[470,451,900,903] else #[407,572,899,904]) else (if i.val < 699 then #[562,489,882,382] else #[563,472,879,905])) else (if i.val < 702 then (if i.val < 701 then #[536,491,872,906] else #[497,899,551,907]) else (if i.val < 703 then #[566,412,458,908] else #[558,494,483,909])))))) else (if i.val < 736 then (if i.val < 720 then (if i.val < 712 then (if i.val < 708 then (if i.val < 706 then (if i.val < 705 then #[893,573,487,910] else #[492,900,157,911]) else (if i.val < 707 then #[906,901,392,912] else #[913,500,912,383])) else (if i.val < 710 then (if i.val < 709 then #[416,561,914,915] else #[896,568,158,913]) else (if i.val < 711 then #[478,417,908,916] else #[419,418,905,917]))) else (if i.val < 716 then (if i.val < 714 then (if i.val < 713 then #[576,506,878,409] else #[577,507,889,411]) else (if i.val < 715 then #[421,420,535,891] else #[579,589,101,587])) else (if i.val < 718 then (if i.val < 717 then #[867,585,570,8] else #[581,866,134,599]) else (if i.val < 719 then #[590,596,617,918] else #[617,607,520,919])))) else (if i.val < 728 then (if i.val < 724 then (if i.val < 722 then (if i.val < 721 then #[431,603,629,920] else #[874,580,909,921]) else (if i.val < 723 then #[884,909,514,922] else #[877,438,901,923])) else (if i.val < 726 then (if i.val < 725 then #[440,439,460,614] else #[589,579,81,870]) else (if i.val < 727 then #[582,869,499,6] else #[543,542,581,505]))) else (if i.val < 732 then (if i.val < 730 then (if i.val < 729 then #[592,872,461,640] else #[593,871,455,619]) else (if i.val < 731 then #[640,908,87,924] else #[597,873,481,925])) else (if i.val < 734 then (if i.val < 733 then #[869,582,925,926] else #[595,875,490,927]) else (if i.val < 735 then #[463,925,584,928] else #[870,456,927,929]))))) else (if i.val < 752 then (if i.val < 744 then (if i.val < 740 then (if i.val < 738 then (if i.val < 737 then #[918,888,620,439] else #[605,879,466,930]) else (if i.val < 739 then #[925,463,870,931] else #[459,584,930,932])) else (if i.val < 742 then (if i.val < 741 then #[611,921,916,440] else #[601,883,472,933]) else (if i.val < 743 then #[636,930,582,934] else #[927,583,869,935]))) else (if i.val < 748 then (if i.val < 746 then (if i.val < 745 then #[608,922,500,441] else #[465,464,933,936]) else (if i.val < 747 then #[920,878,641,110] else #[604,923,903,378])) else (if i.val < 750 then (if i.val < 749 then #[485,474,505,937] else #[468,467,866,575]) else (if i.val < 751 then #[614,891,543,609] else #[615,892,932,443])))) else (if i.val < 760 then (if i.val < 756 then (if i.val < 754 then (if i.val < 753 then #[495,619,488,938] else #[583,927,464,939]) else (if i.val < 755 then #[940,895,939,444] else #[503,616,159,940])) else (if i.val < 758 then (if i.val < 757 then #[620,897,920,424] else #[621,898,936,471]) else (if i.val < 759 then #[900,492,478,941] else #[899,497,419,942]))) else (if i.val < 764 then (if i.val < 762 then (if i.val < 761 then #[933,499,459,943] else #[633,902,943,446]) else (if i.val < 763 then #[626,903,921,432] else #[627,904,926,480])) else (if i.val < 766 then (if i.val < 765 then #[908,640,470,944] else #[499,933,456,945]) else (if i.val < 767 then #[946,907,945,448] else #[905,639,407,947])))))))) else (if i.val < 896 then (if i.val < 832 then (if i.val < 800 then (if i.val < 784 then (if i.val < 776 then (if i.val < 772 then (if i.val < 770 then (if i.val < 769 then #[930,636,465,948] else #[625,910,948,449]) else (if i.val < 771 then #[894,885,438,949] else #[950,911,949,403])) else (if i.val < 774 then (if i.val < 773 then #[606,632,431,951] else #[637,949,924,75]) else (if i.val < 775 then #[500,913,951,135] else #[914,631,107,950]))) else (if i.val < 780 then (if i.val < 778 then (if i.val < 777 then #[594,628,141,946] else #[641,915,918,14]) else (if i.val < 779 then #[642,916,923,63] else #[643,917,929,77])) else (if i.val < 782 then (if i.val < 781 then #[866,581,394,877] else #[580,874,894,952]) else (if i.val < 783 then #[514,881,906,953] else #[596,590,632,954])))) else (if i.val < 792 then (if i.val < 788 then (if i.val < 786 then (if i.val < 785 then #[599,520,624,955] else #[871,593,536,914]) else (if i.val < 787 then #[872,592,530,896] else #[875,595,555,956])) else (if i.val < 790 then (if i.val < 789 then #[585,867,956,957] else #[873,597,563,958]) else (if i.val < 791 then #[538,956,868,959] else #[587,531,958,960]))) else (if i.val < 796 then (if i.val < 794 then (if i.val < 793 then #[952,610,897,420] else #[883,601,541,961]) else (if i.val < 795 then #[956,538,587,962] else #[534,868,961,963])) else (if i.val < 798 then (if i.val < 797 then #[889,954,642,421] else #[879,605,547,964]) else (if i.val < 799 then #[586,961,867,965] else #[958,634,585,966]))))) else (if i.val < 816 then (if i.val < 808 then (if i.val < 804 then (if i.val < 802 then (if i.val < 801 then #[886,951,571,422] else #[540,539,964,967]) else (if i.val < 803 then #[953,600,915,372] else #[882,955,626,116])) else (if i.val < 806 then (if i.val < 805 then #[559,549,575,968] else #[891,614,468,887]) else (if i.val < 807 then #[892,615,963,521] else #[568,896,561,969]))) else (if i.val < 812 then (if i.val < 810 then (if i.val < 809 then #[634,958,539,970] else #[971,618,970,522]) else (if i.val < 811 then #[573,893,418,971] else #[897,620,953,508])) else (if i.val < 814 then (if i.val < 813 then #[898,621,967,546] else #[623,565,552,972]) else (if i.val < 815 then #[622,569,160,973] else #[964,570,534,974])))) else (if i.val < 824 then (if i.val < 820 then (if i.val < 818 then (if i.val < 817 then #[910,625,974,523] else #[903,626,954,515]) else (if i.val < 819 then #[904,627,957,554] else #[631,914,545,975])) else (if i.val < 822 then (if i.val < 821 then #[570,964,531,976] else #[977,630,976,524]) else (if i.val < 823 then #[628,594,147,978] else #[961,586,540,979]))) else (if i.val < 828 then (if i.val < 826 then (if i.val < 825 then #[902,633,979,525] else #[924,635,919,143]) else (if i.val < 827 then #[912,919,950,95] else #[571,638,922,395])) else (if i.val < 830 then (if i.val < 829 then #[639,905,401,977] else #[915,641,952,62]) else (if i.val < 831 then #[916,642,955,15] else #[917,643,960,97])))))) else (if i.val < 864 then (if i.val < 848 then (if i.val < 840 then (if i.val < 836 then (if i.val < 834 then (if i.val < 833 then #[600,953,479,377] else #[919,912,638,379]) else (if i.val < 835 then #[610,952,506,73] else #[923,604,577,373])) else (if i.val < 838 then (if i.val < 837 then #[922,608,635,374] else #[921,611,562,94]) else (if i.val < 839 then #[911,950,608,16] else #[602,598,609,980]))) else (if i.val < 844 then (if i.val < 842 then (if i.val < 841 then #[929,963,621,588] else #[607,617,603,981]) else (if i.val < 843 then #[928,965,630,429] else #[926,967,615,516])) else (if i.val < 846 then (if i.val < 845 then #[632,606,599,982] else #[931,979,625,519]) else (if i.val < 847 then #[936,957,643,425] else #[624,629,596,983])))) else (if i.val < 856 then (if i.val < 852 then (if i.val < 850 then (if i.val < 849 then #[934,959,618,426] else #[935,974,633,517]) else (if i.val < 851 then #[932,960,627,124] else #[938,968,981,148])) else (if i.val < 854 then (if i.val < 853 then #[937,969,980,142] else #[939,976,946,129]) else (if i.val < 855 then #[618,971,928,82] else #[944,972,983,136]))) else (if i.val < 860 then (if i.val < 858 then (if i.val < 857 then #[947,973,966,103] else #[943,966,978,127]) else (if i.val < 859 then #[941,975,982,133] else #[945,970,940,125])) else (if i.val < 862 then (if i.val < 861 then #[630,977,934,78] else #[942,978,962,100]) else (if i.val < 863 then #[948,962,973,130] else #[949,637,913,117]))))) else (if i.val < 880 then (if i.val < 872 then (if i.val < 868 then (if i.val < 866 then (if i.val < 865 then #[635,924,886,64] else #[951,886,911,112]) else (if i.val < 867 then #[780,717,257,791] else #[716,788,808,984])) else (if i.val < 870 then (if i.val < 869 then #[650,795,820,985] else #[732,726,768,986]) else (if i.val < 871 then #[735,656,760,987] else #[785,729,672,828]))) else (if i.val < 876 then (if i.val < 874 then (if i.val < 873 then #[786,728,666,810] else #[789,731,691,988]) else (if i.val < 875 then #[721,781,988,989] else #[787,733,699,990])) else (if i.val < 878 then (if i.val < 877 then #[674,988,782,991] else #[723,667,990,992]) else (if i.val < 879 then #[984,746,811,283] else #[797,737,677,993])))) else (if i.val < 888 then (if i.val < 884 then (if i.val < 882 then (if i.val < 881 then #[988,674,723,994] else #[670,782,993,995]) else (if i.val < 883 then #[803,986,778,284] else #[793,741,683,996])) else (if i.val < 886 then (if i.val < 885 then #[722,993,781,997] else #[990,770,721,998]) else (if i.val < 887 then #[800,865,707,285] else #[676,675,996,999]))) else (if i.val < 892 then (if i.val < 890 then (if i.val < 889 then #[985,736,829,235] else #[796,987,762,189]) else (if i.val < 891 then #[695,685,711,1000] else #[805,750,331,801])) else (if i.val < 894 then (if i.val < 893 then #[806,751,995,657] else #[704,810,697,1001]) else (if i.val < 895 then #[770,990,675,1002] else #[1003,754,1002,658]))))))) else (if i.val < 960 then (if i.val < 928 then (if i.val < 912 then (if i.val < 904 then (if i.val < 900 then (if i.val < 898 then (if i.val < 897 then #[709,807,281,1003] else #[811,756,985,644]) else (if i.val < 899 then #[812,757,999,682] else #[759,701,688,1004])) else (if i.val < 902 then (if i.val < 901 then #[758,705,233,1005] else #[996,706,670,1006]) else (if i.val < 903 then #[824,761,1006,659] else #[817,762,986,651]))) else (if i.val < 908 then (if i.val < 906 then (if i.val < 905 then #[818,763,989,690] else #[767,828,681,1007]) else (if i.val < 907 then #[706,996,667,1008] else #[1009,766,1008,660])) else (if i.val < 910 then (if i.val < 909 then #[764,730,220,1010] else #[993,722,676,1011]) else (if i.val < 911 then #[816,769,1011,661] else #[838,771,833,216])))) else (if i.val < 920 then (if i.val < 916 then (if i.val < 914 then (if i.val < 913 then #[826,833,864,168] else #[707,774,836,258]) else (if i.val < 915 then #[775,819,264,1009] else #[829,777,984,32])) else (if i.val < 918 then (if i.val < 917 then #[830,778,987,25] else #[831,779,992,170]) else (if i.val < 919 then #[736,985,342,240] else #[833,826,774,242]))) else (if i.val < 924 then (if i.val < 922 then (if i.val < 921 then #[746,984,369,43] else #[837,740,713,236]) else (if i.val < 923 then #[836,744,771,237] else #[835,747,698,167])) else (if i.val < 926 then (if i.val < 925 then #[825,864,744,26] else #[738,734,745,1012]) else (if i.val < 927 then #[843,995,757,724] else #[743,753,739,1013]))))) else (if i.val < 944 then (if i.val < 936 then (if i.val < 932 then (if i.val < 930 then (if i.val < 929 then #[842,997,766,292] else #[840,999,751,652]) else (if i.val < 931 then #[768,742,735,1014] else #[845,1011,761,655])) else (if i.val < 934 then (if i.val < 933 then #[850,989,779,288] else #[760,765,732,1015]) else (if i.val < 935 then #[848,991,754,289] else #[849,1006,769,653]))) else (if i.val < 940 then (if i.val < 938 then (if i.val < 937 then #[846,992,763,197] else #[852,1000,1013,221]) else (if i.val < 939 then #[851,1001,1012,215] else #[853,1008,860,202])) else (if i.val < 942 then (if i.val < 941 then #[754,1003,842,52] else #[858,1004,1015,209]) else (if i.val < 943 then #[861,1005,998,176] else #[857,998,1010,200])))) else (if i.val < 952 then (if i.val < 948 then (if i.val < 946 then (if i.val < 945 then #[855,1007,1014,206] else #[859,1002,854,198]) else (if i.val < 947 then #[766,1009,848,48] else #[856,1010,994,173])) else (if i.val < 950 then (if i.val < 949 then #[862,994,1005,203] else #[863,773,827,190]) else (if i.val < 951 then #[771,838,800,34] else #[865,800,825,185]))) else (if i.val < 956 then (if i.val < 954 then (if i.val < 953 then #[792,834,689,188] else #[802,832,712,166]) else (if i.val < 955 then #[987,796,370,184] else #[986,803,352,44])) else (if i.val < 958 then (if i.val < 957 then #[794,790,801,1016] else #[992,846,812,714]) else (if i.val < 959 then #[799,808,795,1017] else #[991,848,821,649])))))) else (if i.val < 992 then (if i.val < 976 then (if i.val < 968 then (if i.val < 964 then (if i.val < 962 then (if i.val < 961 then #[989,850,806,296] else #[823,798,791,1018]) else (if i.val < 963 then #[994,862,816,299] else #[999,840,831,645])) else (if i.val < 966 then (if i.val < 965 then #[815,820,788,1019] else #[997,842,809,646]) else (if i.val < 967 then #[998,857,824,297] else #[995,843,818,247]))) else (if i.val < 972 then (if i.val < 970 then (if i.val < 969 then #[1001,851,1017,271] else #[1000,852,1016,265]) else (if i.val < 971 then #[1002,859,1009,252] else #[809,854,991,175])) else (if i.val < 974 then (if i.val < 973 then #[1007,855,1019,259] else #[1010,856,849,53]) else (if i.val < 975 then #[1006,849,861,250] else #[1004,858,1018,256])))) else (if i.val < 984 then (if i.val < 980 then (if i.val < 978 then (if i.val < 977 then #[1008,853,1003,248] else #[821,860,997,171]) else (if i.val < 979 then #[1005,861,845,50] else #[1011,845,856,253])) else (if i.val < 982 then (if i.val < 981 then #[1012,1018,855,323] else #[1013,1019,858,320]) else (if i.val < 983 then #[1014,1016,851,317] else #[1015,1017,852,315]))) else (if i.val < 988 then (if i.val < 986 then (if i.val < 985 then #[878,920,553,115] else #[888,918,576,93]) else (if i.val < 987 then #[955,882,507,111] else #[954,889,489,74])) else (if i.val < 990 then (if i.val < 989 then #[880,876,887,1020] else #[960,932,898,578]) else (if i.val < 991 then #[885,894,881,1021] else #[959,934,907,513]))))) else (if i.val < 1008 then (if i.val < 1000 then (if i.val < 996 then (if i.val < 994 then (if i.val < 993 then #[957,936,892,433] else #[909,884,877,1022]) else (if i.val < 995 then #[962,948,902,436] else #[967,926,917,509])) else (if i.val < 998 then (if i.val < 997 then #[901,906,874,1023] else #[965,928,895,510]) else (if i.val < 999 then #[966,943,910,434] else #[963,929,904,384]))) else (if i.val < 1004 then (if i.val < 1002 then (if i.val < 1001 then #[969,937,1021,408] else #[968,938,1020,402]) else (if i.val < 1003 then #[970,945,977,389] else #[895,940,959,102])) else (if i.val < 1006 then (if i.val < 1005 then #[975,941,1023,396] else #[978,942,935,83]) else (if i.val < 1007 then #[974,935,947,387] else #[972,944,1022,393])))) else (if i.val < 1016 then (if i.val < 1012 then (if i.val < 1010 then (if i.val < 1009 then #[976,939,971,385] else #[907,946,965,98]) else (if i.val < 1011 then #[973,947,931,80] else #[979,931,942,390])) else (if i.val < 1014 then (if i.val < 1013 then #[980,1022,941,460] else #[981,1023,944,457]) else (if i.val < 1015 then #[982,1020,937,454] else #[983,1021,938,452]))) else (if i.val < 1020 then (if i.val < 1018 then (if i.val < 1017 then #[1020,982,972,535] else #[1021,983,975,532]) else (if i.val < 1019 then #[1022,980,968,529] else #[1023,981,969,527])) else (if i.val < 1022 then (if i.val < 1021 then #[1016,1014,1004,671] else #[1017,1015,1007,668]) else (if i.val < 1023 then #[1018,1012,1000,665] else #[1019,1013,1001,663]))))))))))
private def alphaWordTable (i : Fin 1024) : List (Fin 4) :=
  (if i.val < 512 then (if i.val < 256 then (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then [] else [0]) else (if i.val < 3 then [1] else [2])) else (if i.val < 6 then (if i.val < 5 then [3] else [0,1]) else (if i.val < 7 then [0,2] else [0,3]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then [1,2] else [1,3]) else (if i.val < 11 then [2,0] else [2,1])) else (if i.val < 14 then (if i.val < 13 then [2,2] else [2,3]) else (if i.val < 15 then [3,0] else [3,1])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then [3,2] else [3,3]) else (if i.val < 19 then [0,1,2] else [0,1,3])) else (if i.val < 22 then (if i.val < 21 then [0,2,0] else [0,2,1]) else (if i.val < 23 then [0,2,2] else [0,2,3]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then [0,3,0] else [0,3,1]) else (if i.val < 27 then [0,3,2] else [0,3,3])) else (if i.val < 30 then (if i.val < 29 then [1,2,0] else [1,2,1]) else (if i.val < 31 then [1,2,2] else [1,2,3]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then [1,3,0] else [1,3,1]) else (if i.val < 35 then [1,3,2] else [1,3,3])) else (if i.val < 38 then (if i.val < 37 then [2,0,1] else [2,0,2]) else (if i.val < 39 then [2,0,3] else [2,1,2]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then [2,1,3] else [2,2,2]) else (if i.val < 43 then [2,2,3] else [2,3,0])) else (if i.val < 46 then (if i.val < 45 then [2,3,1] else [2,3,2]) else (if i.val < 47 then [2,3,3] else [3,0,1])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then [3,0,2] else [3,0,3]) else (if i.val < 51 then [3,1,2] else [3,1,3])) else (if i.val < 54 then (if i.val < 53 then [3,2,0] else [3,2,1]) else (if i.val < 55 then [3,2,3] else [3,3,0]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then [3,3,1] else [3,3,3]) else (if i.val < 59 then [0,1,2,0] else [0,1,2,1])) else (if i.val < 62 then (if i.val < 61 then [0,1,2,2] else [0,1,2,3]) else (if i.val < 63 then [0,1,3,0] else [0,1,3,1])))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then [0,1,3,2] else [0,1,3,3]) else (if i.val < 67 then [0,2,0,1] else [0,2,0,2])) else (if i.val < 70 then (if i.val < 69 then [0,2,0,3] else [0,2,1,2]) else (if i.val < 71 then [0,2,1,3] else [0,2,2,2]))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then [0,2,2,3] else [0,2,3,0]) else (if i.val < 75 then [0,2,3,1] else [0,2,3,2])) else (if i.val < 78 then (if i.val < 77 then [0,2,3,3] else [0,3,0,1]) else (if i.val < 79 then [0,3,0,2] else [0,3,0,3])))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then [0,3,1,2] else [0,3,1,3]) else (if i.val < 83 then [0,3,2,0] else [0,3,2,1])) else (if i.val < 86 then (if i.val < 85 then [0,3,2,3] else [0,3,3,0]) else (if i.val < 87 then [0,3,3,1] else [0,3,3,3]))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then [1,2,0,2] else [1,2,0,3]) else (if i.val < 91 then [1,2,1,2] else [1,2,1,3])) else (if i.val < 94 then (if i.val < 93 then [1,2,2,3] else [1,2,3,0]) else (if i.val < 95 then [1,2,3,1] else [1,2,3,2]))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then [1,2,3,3] else [1,3,0,1]) else (if i.val < 99 then [1,3,0,2] else [1,3,0,3])) else (if i.val < 102 then (if i.val < 101 then [1,3,1,2] else [1,3,1,3]) else (if i.val < 103 then [1,3,2,0] else [1,3,2,1]))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then [1,3,2,3] else [1,3,3,0]) else (if i.val < 107 then [1,3,3,1] else [1,3,3,3])) else (if i.val < 110 then (if i.val < 109 then [2,0,1,3] else [2,0,2,3]) else (if i.val < 111 then [2,0,3,0] else [2,0,3,1])))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then [2,0,3,2] else [2,0,3,3]) else (if i.val < 115 then [2,1,2,3] else [2,1,3,0])) else (if i.val < 118 then (if i.val < 117 then [2,1,3,1] else [2,1,3,2]) else (if i.val < 119 then [2,1,3,3] else [2,2,2,3]))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then [2,2,3,0] else [2,2,3,1]) else (if i.val < 123 then [2,2,3,2] else [2,2,3,3])) else (if i.val < 126 then (if i.val < 125 then [2,3,0,1] else [2,3,0,2]) else (if i.val < 127 then [2,3,0,3] else [2,3,1,2]))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then [2,3,1,3] else [2,3,2,0]) else (if i.val < 131 then [2,3,2,1] else [2,3,2,3])) else (if i.val < 134 then (if i.val < 133 then [2,3,3,3] else [3,0,1,2]) else (if i.val < 135 then [3,0,1,3] else [3,0,2,0]))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then [3,0,2,1] else [3,0,2,3]) else (if i.val < 139 then [3,0,3,0] else [3,0,3,1])) else (if i.val < 142 then (if i.val < 141 then [3,0,3,2] else [3,0,3,3]) else (if i.val < 143 then [3,1,2,0] else [3,1,2,1])))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then [3,1,2,3] else [3,1,3,0]) else (if i.val < 147 then [3,1,3,1] else [3,1,3,3])) else (if i.val < 150 then (if i.val < 149 then [3,2,0,1] else [3,2,0,2]) else (if i.val < 151 then [3,2,0,3] else [3,2,1,2]))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then [3,2,1,3] else [3,2,3,1]) else (if i.val < 155 then [3,2,3,2] else [3,2,3,3])) else (if i.val < 158 then (if i.val < 157 then [3,3,0,1] else [3,3,0,3]) else (if i.val < 159 then [3,3,1,3] else [3,3,3,0]))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then [3,3,3,1] else [0,1,2,0,2]) else (if i.val < 163 then [0,1,2,0,3] else [0,1,2,1,2])) else (if i.val < 166 then (if i.val < 165 then [0,1,2,1,3] else [0,1,2,2,3]) else (if i.val < 167 then [0,1,2,3,0] else [0,1,2,3,1]))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then [0,1,2,3,2] else [0,1,2,3,3]) else (if i.val < 171 then [0,1,3,0,1] else [0,1,3,0,2])) else (if i.val < 174 then (if i.val < 173 then [0,1,3,0,3] else [0,1,3,1,2]) else (if i.val < 175 then [0,1,3,1,3] else [0,1,3,2,0])))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then [0,1,3,2,1] else [0,1,3,2,3]) else (if i.val < 179 then [0,1,3,3,0] else [0,1,3,3,1])) else (if i.val < 182 then (if i.val < 181 then [0,1,3,3,3] else [0,2,0,1,3]) else (if i.val < 183 then [0,2,0,2,3] else [0,2,0,3,0]))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then [0,2,0,3,1] else [0,2,0,3,2]) else (if i.val < 187 then [0,2,0,3,3] else [0,2,1,2,3])) else (if i.val < 190 then (if i.val < 189 then [0,2,1,3,0] else [0,2,1,3,1]) else (if i.val < 191 then [0,2,1,3,2] else [0,2,1,3,3])))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then [0,2,2,2,3] else [0,2,2,3,0]) else (if i.val < 195 then [0,2,2,3,1] else [0,2,2,3,2])) else (if i.val < 198 then (if i.val < 197 then [0,2,2,3,3] else [0,2,3,0,1]) else (if i.val < 199 then [0,2,3,0,2] else [0,2,3,0,3]))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then [0,2,3,1,2] else [0,2,3,1,3]) else (if i.val < 203 then [0,2,3,2,0] else [0,2,3,2,1])) else (if i.val < 206 then (if i.val < 205 then [0,2,3,2,3] else [0,2,3,3,3]) else (if i.val < 207 then [0,3,0,1,2] else [0,3,0,1,3])))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then [0,3,0,2,0] else [0,3,0,2,1]) else (if i.val < 211 then [0,3,0,2,3] else [0,3,0,3,0])) else (if i.val < 214 then (if i.val < 213 then [0,3,0,3,1] else [0,3,0,3,2]) else (if i.val < 215 then [0,3,0,3,3] else [0,3,1,2,0]))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then [0,3,1,2,1] else [0,3,1,2,3]) else (if i.val < 219 then [0,3,1,3,0] else [0,3,1,3,1])) else (if i.val < 222 then (if i.val < 221 then [0,3,1,3,3] else [0,3,2,0,1]) else (if i.val < 223 then [0,3,2,0,2] else [0,3,2,0,3]))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then [0,3,2,1,2] else [0,3,2,1,3]) else (if i.val < 227 then [0,3,2,3,1] else [0,3,2,3,2])) else (if i.val < 230 then (if i.val < 229 then [0,3,2,3,3] else [0,3,3,0,1]) else (if i.val < 231 then [0,3,3,0,3] else [0,3,3,1,3]))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then [0,3,3,3,0] else [0,3,3,3,1]) else (if i.val < 235 then [1,2,0,2,3] else [1,2,0,3,0])) else (if i.val < 238 then (if i.val < 237 then [1,2,0,3,1] else [1,2,0,3,2]) else (if i.val < 239 then [1,2,0,3,3] else [1,2,1,2,3])))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then [1,2,1,3,0] else [1,2,1,3,1]) else (if i.val < 243 then [1,2,1,3,2] else [1,2,1,3,3])) else (if i.val < 246 then (if i.val < 245 then [1,2,2,3,0] else [1,2,2,3,1]) else (if i.val < 247 then [1,2,2,3,2] else [1,2,3,0,1]))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then [1,2,3,0,2] else [1,2,3,0,3]) else (if i.val < 251 then [1,2,3,1,2] else [1,2,3,1,3])) else (if i.val < 254 then (if i.val < 253 then [1,2,3,2,0] else [1,2,3,2,1]) else (if i.val < 255 then [1,2,3,2,3] else [1,2,3,3,3])))))))) else (if i.val < 384 then (if i.val < 320 then (if i.val < 288 then (if i.val < 272 then (if i.val < 264 then (if i.val < 260 then (if i.val < 258 then (if i.val < 257 then [1,3,0,1,2] else [1,3,0,1,3]) else (if i.val < 259 then [1,3,0,2,0] else [1,3,0,2,1])) else (if i.val < 262 then (if i.val < 261 then [1,3,0,2,3] else [1,3,0,3,0]) else (if i.val < 263 then [1,3,0,3,1] else [1,3,0,3,2]))) else (if i.val < 268 then (if i.val < 266 then (if i.val < 265 then [1,3,0,3,3] else [1,3,1,2,0]) else (if i.val < 267 then [1,3,1,2,1] else [1,3,1,2,3])) else (if i.val < 270 then (if i.val < 269 then [1,3,1,3,0] else [1,3,1,3,1]) else (if i.val < 271 then [1,3,1,3,3] else [1,3,2,0,1])))) else (if i.val < 280 then (if i.val < 276 then (if i.val < 274 then (if i.val < 273 then [1,3,2,0,2] else [1,3,2,0,3]) else (if i.val < 275 then [1,3,2,1,2] else [1,3,2,1,3])) else (if i.val < 278 then (if i.val < 277 then [1,3,2,3,1] else [1,3,2,3,2]) else (if i.val < 279 then [1,3,2,3,3] else [1,3,3,0,3]))) else (if i.val < 284 then (if i.val < 282 then (if i.val < 281 then [1,3,3,1,3] else [1,3,3,3,0]) else (if i.val < 283 then [1,3,3,3,1] else [2,0,1,3,0])) else (if i.val < 286 then (if i.val < 285 then [2,0,1,3,1] else [2,0,1,3,2]) else (if i.val < 287 then [2,0,1,3,3] else [2,0,2,3,0]))))) else (if i.val < 304 then (if i.val < 296 then (if i.val < 292 then (if i.val < 290 then (if i.val < 289 then [2,0,3,0,1] else [2,0,3,0,2]) else (if i.val < 291 then [2,0,3,0,3] else [2,0,3,1,3])) else (if i.val < 294 then (if i.val < 293 then [2,0,3,2,0] else [2,0,3,2,3]) else (if i.val < 295 then [2,0,3,3,3] else [2,1,2,3,1]))) else (if i.val < 300 then (if i.val < 298 then (if i.val < 297 then [2,1,3,0,1] else [2,1,3,1,2]) else (if i.val < 299 then [2,1,3,1,3] else [2,1,3,2,1])) else (if i.val < 302 then (if i.val < 301 then [2,1,3,2,3] else [2,1,3,3,3]) else (if i.val < 303 then [2,2,2,3,0] else [2,2,2,3,1])))) else (if i.val < 312 then (if i.val < 308 then (if i.val < 306 then (if i.val < 305 then [2,2,2,3,2] else [2,2,2,3,3]) else (if i.val < 307 then [2,2,3,0,1] else [2,2,3,0,2])) else (if i.val < 310 then (if i.val < 309 then [2,2,3,0,3] else [2,2,3,1,2]) else (if i.val < 311 then [2,2,3,1,3] else [2,2,3,2,0]))) else (if i.val < 316 then (if i.val < 314 then (if i.val < 313 then [2,2,3,2,1] else [2,2,3,2,3]) else (if i.val < 315 then [2,2,3,3,3] else [2,3,0,1,2])) else (if i.val < 318 then (if i.val < 317 then [2,3,0,1,3] else [2,3,0,2,1]) else (if i.val < 319 then [2,3,0,2,3] else [2,3,0,3,3])))))) else (if i.val < 352 then (if i.val < 336 then (if i.val < 328 then (if i.val < 324 then (if i.val < 322 then (if i.val < 321 then [2,3,1,2,0] else [2,3,1,2,3]) else (if i.val < 323 then [2,3,1,3,3] else [2,3,2,0,1])) else (if i.val < 326 then (if i.val < 325 then [2,3,2,0,3] else [2,3,2,1,3]) else (if i.val < 327 then [2,3,2,3,3] else [2,3,3,3,0]))) else (if i.val < 332 then (if i.val < 330 then (if i.val < 329 then [2,3,3,3,1] else [3,0,1,2,3]) else (if i.val < 331 then [3,0,1,3,0] else [3,0,1,3,1])) else (if i.val < 334 then (if i.val < 333 then [3,0,1,3,2] else [3,0,1,3,3]) else (if i.val < 335 then [3,0,2,1,2] else [3,0,2,1,3])))) else (if i.val < 344 then (if i.val < 340 then (if i.val < 338 then (if i.val < 337 then [3,0,2,3,2] else [3,0,2,3,3]) else (if i.val < 339 then [3,0,3,0,1] else [3,0,3,0,2])) else (if i.val < 342 then (if i.val < 341 then [3,0,3,0,3] else [3,0,3,3,1]) else (if i.val < 343 then [3,0,3,3,3] else [3,1,2,0,2]))) else (if i.val < 348 then (if i.val < 346 then (if i.val < 345 then [3,1,2,0,3] else [3,1,2,1,3]) else (if i.val < 347 then [3,1,2,3,1] else [3,1,2,3,2])) else (if i.val < 350 then (if i.val < 349 then [3,1,2,3,3] else [3,1,3,0,1]) else (if i.val < 351 then [3,1,3,1,3] else [3,1,3,3,0]))))) else (if i.val < 368 then (if i.val < 360 then (if i.val < 356 then (if i.val < 354 then (if i.val < 353 then [3,1,3,3,3] else [3,2,0,1,3]) else (if i.val < 355 then [3,2,0,3,2] else [3,2,0,3,3])) else (if i.val < 358 then (if i.val < 357 then [3,2,1,3,1] else [3,2,1,3,2]) else (if i.val < 359 then [3,2,1,3,3] else [3,2,3,1,2]))) else (if i.val < 364 then (if i.val < 362 then (if i.val < 361 then [3,2,3,1,3] else [3,2,3,2,0]) else (if i.val < 363 then [3,2,3,2,3] else [3,2,3,3,3])) else (if i.val < 366 then (if i.val < 365 then [3,3,0,1,3] else [3,3,0,3,0]) else (if i.val < 367 then [3,3,0,3,2] else [3,3,1,3,1])))) else (if i.val < 376 then (if i.val < 372 then (if i.val < 370 then (if i.val < 369 then [3,3,3,0,1] else [3,3,3,0,3]) else (if i.val < 371 then [3,3,3,1,3] else [0,1,2,0,2,3])) else (if i.val < 374 then (if i.val < 373 then [0,1,2,0,3,0] else [0,1,2,0,3,1]) else (if i.val < 375 then [0,1,2,0,3,2] else [0,1,2,0,3,3]))) else (if i.val < 380 then (if i.val < 378 then (if i.val < 377 then [0,1,2,1,2,3] else [0,1,2,1,3,0]) else (if i.val < 379 then [0,1,2,1,3,1] else [0,1,2,1,3,2])) else (if i.val < 382 then (if i.val < 381 then [0,1,2,1,3,3] else [0,1,2,2,3,0]) else (if i.val < 383 then [0,1,2,2,3,1] else [0,1,2,2,3,2]))))))) else (if i.val < 448 then (if i.val < 416 then (if i.val < 400 then (if i.val < 392 then (if i.val < 388 then (if i.val < 386 then (if i.val < 385 then [0,1,2,3,0,1] else [0,1,2,3,0,2]) else (if i.val < 387 then [0,1,2,3,0,3] else [0,1,2,3,1,2])) else (if i.val < 390 then (if i.val < 389 then [0,1,2,3,1,3] else [0,1,2,3,2,0]) else (if i.val < 391 then [0,1,2,3,2,1] else [0,1,2,3,2,3]))) else (if i.val < 396 then (if i.val < 394 then (if i.val < 393 then [0,1,2,3,3,3] else [0,1,3,0,1,2]) else (if i.val < 395 then [0,1,3,0,1,3] else [0,1,3,0,2,0])) else (if i.val < 398 then (if i.val < 397 then [0,1,3,0,2,1] else [0,1,3,0,2,3]) else (if i.val < 399 then [0,1,3,0,3,0] else [0,1,3,0,3,1])))) else (if i.val < 408 then (if i.val < 404 then (if i.val < 402 then (if i.val < 401 then [0,1,3,0,3,2] else [0,1,3,0,3,3]) else (if i.val < 403 then [0,1,3,1,2,0] else [0,1,3,1,2,1])) else (if i.val < 406 then (if i.val < 405 then [0,1,3,1,2,3] else [0,1,3,1,3,0]) else (if i.val < 407 then [0,1,3,1,3,1] else [0,1,3,1,3,3]))) else (if i.val < 412 then (if i.val < 410 then (if i.val < 409 then [0,1,3,2,0,1] else [0,1,3,2,0,2]) else (if i.val < 411 then [0,1,3,2,0,3] else [0,1,3,2,1,2])) else (if i.val < 414 then (if i.val < 413 then [0,1,3,2,1,3] else [0,1,3,2,3,1]) else (if i.val < 415 then [0,1,3,2,3,2] else [0,1,3,2,3,3]))))) else (if i.val < 432 then (if i.val < 424 then (if i.val < 420 then (if i.val < 418 then (if i.val < 417 then [0,1,3,3,0,3] else [0,1,3,3,1,3]) else (if i.val < 419 then [0,1,3,3,3,0] else [0,1,3,3,3,1])) else (if i.val < 422 then (if i.val < 421 then [0,2,0,1,3,0] else [0,2,0,1,3,1]) else (if i.val < 423 then [0,2,0,1,3,2] else [0,2,0,1,3,3]))) else (if i.val < 428 then (if i.val < 426 then (if i.val < 425 then [0,2,0,2,3,0] else [0,2,0,3,0,1]) else (if i.val < 427 then [0,2,0,3,0,2] else [0,2,0,3,0,3])) else (if i.val < 430 then (if i.val < 429 then [0,2,0,3,1,3] else [0,2,0,3,2,0]) else (if i.val < 431 then [0,2,0,3,2,3] else [0,2,0,3,3,3])))) else (if i.val < 440 then (if i.val < 436 then (if i.val < 434 then (if i.val < 433 then [0,2,1,2,3,1] else [0,2,1,3,0,1]) else (if i.val < 435 then [0,2,1,3,1,2] else [0,2,1,3,1,3])) else (if i.val < 438 then (if i.val < 437 then [0,2,1,3,2,1] else [0,2,1,3,2,3]) else (if i.val < 439 then [0,2,1,3,3,3] else [0,2,2,2,3,0]))) else (if i.val < 444 then (if i.val < 442 then (if i.val < 441 then [0,2,2,2,3,1] else [0,2,2,2,3,2]) else (if i.val < 443 then [0,2,2,2,3,3] else [0,2,2,3,0,1])) else (if i.val < 446 then (if i.val < 445 then [0,2,2,3,0,2] else [0,2,2,3,0,3]) else (if i.val < 447 then [0,2,2,3,1,2] else [0,2,2,3,1,3])))))) else (if i.val < 480 then (if i.val < 464 then (if i.val < 456 then (if i.val < 452 then (if i.val < 450 then (if i.val < 449 then [0,2,2,3,2,0] else [0,2,2,3,2,1]) else (if i.val < 451 then [0,2,2,3,2,3] else [0,2,2,3,3,3])) else (if i.val < 454 then (if i.val < 453 then [0,2,3,0,1,2] else [0,2,3,0,1,3]) else (if i.val < 455 then [0,2,3,0,2,1] else [0,2,3,0,2,3]))) else (if i.val < 460 then (if i.val < 458 then (if i.val < 457 then [0,2,3,0,3,3] else [0,2,3,1,2,0]) else (if i.val < 459 then [0,2,3,1,2,3] else [0,2,3,1,3,3])) else (if i.val < 462 then (if i.val < 461 then [0,2,3,2,0,1] else [0,2,3,2,0,3]) else (if i.val < 463 then [0,2,3,2,1,3] else [0,2,3,2,3,3])))) else (if i.val < 472 then (if i.val < 468 then (if i.val < 466 then (if i.val < 465 then [0,2,3,3,3,0] else [0,2,3,3,3,1]) else (if i.val < 467 then [0,3,0,1,2,3] else [0,3,0,1,3,0])) else (if i.val < 470 then (if i.val < 469 then [0,3,0,1,3,1] else [0,3,0,1,3,2]) else (if i.val < 471 then [0,3,0,1,3,3] else [0,3,0,2,1,2]))) else (if i.val < 476 then (if i.val < 474 then (if i.val < 473 then [0,3,0,2,1,3] else [0,3,0,2,3,2]) else (if i.val < 475 then [0,3,0,2,3,3] else [0,3,0,3,0,1])) else (if i.val < 478 then (if i.val < 477 then [0,3,0,3,0,2] else [0,3,0,3,0,3]) else (if i.val < 479 then [0,3,0,3,3,1] else [0,3,0,3,3,3]))))) else (if i.val < 496 then (if i.val < 488 then (if i.val < 484 then (if i.val < 482 then (if i.val < 481 then [0,3,1,2,0,2] else [0,3,1,2,0,3]) else (if i.val < 483 then [0,3,1,2,1,3] else [0,3,1,2,3,1])) else (if i.val < 486 then (if i.val < 485 then [0,3,1,2,3,2] else [0,3,1,2,3,3]) else (if i.val < 487 then [0,3,1,3,0,1] else [0,3,1,3,1,3]))) else (if i.val < 492 then (if i.val < 490 then (if i.val < 489 then [0,3,1,3,3,0] else [0,3,1,3,3,3]) else (if i.val < 491 then [0,3,2,0,1,3] else [0,3,2,0,3,2])) else (if i.val < 494 then (if i.val < 493 then [0,3,2,0,3,3] else [0,3,2,1,3,1]) else (if i.val < 495 then [0,3,2,1,3,2] else [0,3,2,1,3,3])))) else (if i.val < 504 then (if i.val < 500 then (if i.val < 498 then (if i.val < 497 then [0,3,2,3,1,2] else [0,3,2,3,1,3]) else (if i.val < 499 then [0,3,2,3,2,0] else [0,3,2,3,2,3])) else (if i.val < 502 then (if i.val < 501 then [0,3,2,3,3,3] else [0,3,3,0,1,3]) else (if i.val < 503 then [0,3,3,0,3,0] else [0,3,3,0,3,2]))) else (if i.val < 508 then (if i.val < 506 then (if i.val < 505 then [0,3,3,1,3,1] else [0,3,3,3,0,1]) else (if i.val < 507 then [0,3,3,3,0,3] else [0,3,3,3,1,3])) else (if i.val < 510 then (if i.val < 509 then [1,2,0,2,3,0] else [1,2,0,3,0,1]) else (if i.val < 511 then [1,2,0,3,0,2] else [1,2,0,3,0,3]))))))))) else (if i.val < 768 then (if i.val < 640 then (if i.val < 576 then (if i.val < 544 then (if i.val < 528 then (if i.val < 520 then (if i.val < 516 then (if i.val < 514 then (if i.val < 513 then [1,2,0,3,1,3] else [1,2,0,3,2,0]) else (if i.val < 515 then [1,2,0,3,3,3] else [1,2,1,2,3,1])) else (if i.val < 518 then (if i.val < 517 then [1,2,1,3,0,1] else [1,2,1,3,1,2]) else (if i.val < 519 then [1,2,1,3,1,3] else [1,2,1,3,2,1]))) else (if i.val < 524 then (if i.val < 522 then (if i.val < 521 then [1,2,1,3,3,3] else [1,2,2,3,0,1]) else (if i.val < 523 then [1,2,2,3,0,2] else [1,2,2,3,1,2])) else (if i.val < 526 then (if i.val < 525 then [1,2,2,3,2,0] else [1,2,2,3,2,1]) else (if i.val < 527 then [1,2,2,3,2,3] else [1,2,3,0,1,2])))) else (if i.val < 536 then (if i.val < 532 then (if i.val < 530 then (if i.val < 529 then [1,2,3,0,1,3] else [1,2,3,0,2,1]) else (if i.val < 531 then [1,2,3,0,2,3] else [1,2,3,0,3,3])) else (if i.val < 534 then (if i.val < 533 then [1,2,3,1,2,0] else [1,2,3,1,2,3]) else (if i.val < 535 then [1,2,3,1,3,3] else [1,2,3,2,0,1]))) else (if i.val < 540 then (if i.val < 538 then (if i.val < 537 then [1,2,3,2,0,3] else [1,2,3,2,1,3]) else (if i.val < 539 then [1,2,3,2,3,3] else [1,2,3,3,3,0])) else (if i.val < 542 then (if i.val < 541 then [1,2,3,3,3,1] else [1,3,0,1,2,3]) else (if i.val < 543 then [1,3,0,1,3,0] else [1,3,0,1,3,1]))))) else (if i.val < 560 then (if i.val < 552 then (if i.val < 548 then (if i.val < 546 then (if i.val < 545 then [1,3,0,1,3,2] else [1,3,0,1,3,3]) else (if i.val < 547 then [1,3,0,2,1,2] else [1,3,0,2,1,3])) else (if i.val < 550 then (if i.val < 549 then [1,3,0,2,3,2] else [1,3,0,2,3,3]) else (if i.val < 551 then [1,3,0,3,0,2] else [1,3,0,3,0,3]))) else (if i.val < 556 then (if i.val < 554 then (if i.val < 553 then [1,3,0,3,3,1] else [1,3,0,3,3,3]) else (if i.val < 555 then [1,3,1,2,0,2] else [1,3,1,2,0,3])) else (if i.val < 558 then (if i.val < 557 then [1,3,1,2,1,3] else [1,3,1,2,3,1]) else (if i.val < 559 then [1,3,1,2,3,2] else [1,3,1,2,3,3])))) else (if i.val < 568 then (if i.val < 564 then (if i.val < 562 then (if i.val < 561 then [1,3,1,3,1,3] else [1,3,1,3,3,0]) else (if i.val < 563 then [1,3,1,3,3,3] else [1,3,2,0,1,3])) else (if i.val < 566 then (if i.val < 565 then [1,3,2,0,3,2] else [1,3,2,0,3,3]) else (if i.val < 567 then [1,3,2,1,3,1] else [1,3,2,1,3,2]))) else (if i.val < 572 then (if i.val < 570 then (if i.val < 569 then [1,3,2,1,3,3] else [1,3,2,3,1,3]) else (if i.val < 571 then [1,3,2,3,2,3] else [1,3,2,3,3,3])) else (if i.val < 574 then (if i.val < 573 then [1,3,3,0,3,0] else [1,3,3,0,3,2]) else (if i.val < 575 then [1,3,3,1,3,1] else [1,3,3,3,0,1])))))) else (if i.val < 608 then (if i.val < 592 then (if i.val < 584 then (if i.val < 580 then (if i.val < 578 then (if i.val < 577 then [1,3,3,3,0,3] else [1,3,3,3,1,3]) else (if i.val < 579 then [2,0,1,3,0,1] else [2,0,1,3,1,3])) else (if i.val < 582 then (if i.val < 581 then [2,0,1,3,3,3] else [2,0,3,0,1,3]) else (if i.val < 583 then [2,0,3,0,3,3] else [2,0,3,2,3,3]))) else (if i.val < 588 then (if i.val < 586 then (if i.val < 585 then [2,0,3,3,3,0] else [2,1,3,1,3,3]) else (if i.val < 587 then [2,1,3,2,3,3] else [2,1,3,3,3,1])) else (if i.val < 590 then (if i.val < 589 then [2,2,2,3,0,1] else [2,2,2,3,1,3]) else (if i.val < 591 then [2,2,2,3,3,3] else [2,2,3,0,1,3])))) else (if i.val < 600 then (if i.val < 596 then (if i.val < 594 then (if i.val < 593 then [2,2,3,0,2,3] else [2,2,3,2,0,3]) else (if i.val < 595 then [2,2,3,2,3,3] else [2,3,0,1,2,3])) else (if i.val < 598 then (if i.val < 597 then [2,3,0,1,3,3] else [2,3,0,2,1,3]) else (if i.val < 599 then [2,3,0,2,3,3] else [2,3,0,3,3,1]))) else (if i.val < 604 then (if i.val < 602 then (if i.val < 601 then [2,3,0,3,3,3] else [2,3,1,2,0,3]) else (if i.val < 603 then [2,3,1,2,3,3] else [2,3,1,3,3,0])) else (if i.val < 606 then (if i.val < 605 then [2,3,1,3,3,3] else [2,3,2,0,1,3]) else (if i.val < 607 then [2,3,2,0,3,3] else [2,3,2,1,3,3]))))) else (if i.val < 624 then (if i.val < 616 then (if i.val < 612 then (if i.val < 610 then (if i.val < 609 then [2,3,2,3,3,3] else [2,3,3,3,0,1]) else (if i.val < 611 then [2,3,3,3,0,3] else [2,3,3,3,1,3])) else (if i.val < 614 then (if i.val < 613 then [3,0,1,2,3,3] else [3,0,1,3,0,1]) else (if i.val < 615 then [3,0,1,3,0,2] else [3,0,1,3,3,3]))) else (if i.val < 620 then (if i.val < 618 then (if i.val < 617 then [3,0,2,1,3,3] else [3,0,2,3,2,3]) else (if i.val < 619 then [3,0,2,3,3,3] else [3,0,3,0,3,2])) else (if i.val < 622 then (if i.val < 621 then [3,0,3,0,3,3] else [3,0,3,3,1,3]) else (if i.val < 623 then [3,1,2,0,3,3] else [3,1,2,3,1,3])))) else (if i.val < 632 then (if i.val < 628 then (if i.val < 626 then (if i.val < 625 then [3,1,2,3,2,3] else [3,1,2,3,3,3]) else (if i.val < 627 then [3,1,3,1,3,3] else [3,1,3,3,0,3])) else (if i.val < 630 then (if i.val < 629 then [3,2,0,1,3,3] else [3,2,0,3,2,3]) else (if i.val < 631 then [3,2,0,3,3,3] else [3,2,1,3,1,3]))) else (if i.val < 636 then (if i.val < 634 then (if i.val < 633 then [3,2,1,3,2,3] else [3,2,1,3,3,3]) else (if i.val < 635 then [3,2,3,1,2,3] else [3,2,3,1,3,3])) else (if i.val < 638 then (if i.val < 637 then [3,2,3,2,0,3] else [3,2,3,2,3,3]) else (if i.val < 639 then [3,2,3,3,3,0] else [3,3,0,1,3,2]))))))) else (if i.val < 704 then (if i.val < 672 then (if i.val < 656 then (if i.val < 648 then (if i.val < 644 then (if i.val < 642 then (if i.val < 641 then [3,3,0,3,0,2] else [3,3,0,3,0,3]) else (if i.val < 643 then [3,3,1,3,1,3] else [3,3,3,0,1,3])) else (if i.val < 646 then (if i.val < 645 then [0,1,2,0,2,3,0] else [0,1,2,0,3,0,1]) else (if i.val < 647 then [0,1,2,0,3,0,2] else [0,1,2,0,3,0,3]))) else (if i.val < 652 then (if i.val < 650 then (if i.val < 649 then [0,1,2,0,3,1,3] else [0,1,2,0,3,2,0]) else (if i.val < 651 then [0,1,2,0,3,3,3] else [0,1,2,1,2,3,1])) else (if i.val < 654 then (if i.val < 653 then [0,1,2,1,3,0,1] else [0,1,2,1,3,1,2]) else (if i.val < 655 then [0,1,2,1,3,1,3] else [0,1,2,1,3,2,1])))) else (if i.val < 664 then (if i.val < 660 then (if i.val < 658 then (if i.val < 657 then [0,1,2,1,3,3,3] else [0,1,2,2,3,0,1]) else (if i.val < 659 then [0,1,2,2,3,0,2] else [0,1,2,2,3,1,2])) else (if i.val < 662 then (if i.val < 661 then [0,1,2,2,3,2,0] else [0,1,2,2,3,2,1]) else (if i.val < 663 then [0,1,2,2,3,2,3] else [0,1,2,3,0,1,2]))) else (if i.val < 668 then (if i.val < 666 then (if i.val < 665 then [0,1,2,3,0,1,3] else [0,1,2,3,0,2,1]) else (if i.val < 667 then [0,1,2,3,0,2,3] else [0,1,2,3,0,3,3])) else (if i.val < 670 then (if i.val < 669 then [0,1,2,3,1,2,0] else [0,1,2,3,1,2,3]) else (if i.val < 671 then [0,1,2,3,1,3,3] else [0,1,2,3,2,0,1]))))) else (if i.val < 688 then (if i.val < 680 then (if i.val < 676 then (if i.val < 674 then (if i.val < 673 then [0,1,2,3,2,0,3] else [0,1,2,3,2,1,3]) else (if i.val < 675 then [0,1,2,3,2,3,3] else [0,1,2,3,3,3,0])) else (if i.val < 678 then (if i.val < 677 then [0,1,2,3,3,3,1] else [0,1,3,0,1,2,3]) else (if i.val < 679 then [0,1,3,0,1,3,0] else [0,1,3,0,1,3,1]))) else (if i.val < 684 then (if i.val < 682 then (if i.val < 681 then [0,1,3,0,1,3,2] else [0,1,3,0,1,3,3]) else (if i.val < 683 then [0,1,3,0,2,1,2] else [0,1,3,0,2,1,3])) else (if i.val < 686 then (if i.val < 685 then [0,1,3,0,2,3,2] else [0,1,3,0,2,3,3]) else (if i.val < 687 then [0,1,3,0,3,0,2] else [0,1,3,0,3,0,3])))) else (if i.val < 696 then (if i.val < 692 then (if i.val < 690 then (if i.val < 689 then [0,1,3,0,3,3,1] else [0,1,3,0,3,3,3]) else (if i.val < 691 then [0,1,3,1,2,0,2] else [0,1,3,1,2,0,3])) else (if i.val < 694 then (if i.val < 693 then [0,1,3,1,2,1,3] else [0,1,3,1,2,3,1]) else (if i.val < 695 then [0,1,3,1,2,3,2] else [0,1,3,1,2,3,3]))) else (if i.val < 700 then (if i.val < 698 then (if i.val < 697 then [0,1,3,1,3,1,3] else [0,1,3,1,3,3,0]) else (if i.val < 699 then [0,1,3,1,3,3,3] else [0,1,3,2,0,1,3])) else (if i.val < 702 then (if i.val < 701 then [0,1,3,2,0,3,2] else [0,1,3,2,0,3,3]) else (if i.val < 703 then [0,1,3,2,1,3,1] else [0,1,3,2,1,3,2])))))) else (if i.val < 736 then (if i.val < 720 then (if i.val < 712 then (if i.val < 708 then (if i.val < 706 then (if i.val < 705 then [0,1,3,2,1,3,3] else [0,1,3,2,3,1,3]) else (if i.val < 707 then [0,1,3,2,3,2,3] else [0,1,3,2,3,3,3])) else (if i.val < 710 then (if i.val < 709 then [0,1,3,3,0,3,0] else [0,1,3,3,0,3,2]) else (if i.val < 711 then [0,1,3,3,1,3,1] else [0,1,3,3,3,0,1]))) else (if i.val < 716 then (if i.val < 714 then (if i.val < 713 then [0,1,3,3,3,0,3] else [0,1,3,3,3,1,3]) else (if i.val < 715 then [0,2,0,1,3,0,1] else [0,2,0,1,3,1,3])) else (if i.val < 718 then (if i.val < 717 then [0,2,0,1,3,3,3] else [0,2,0,3,0,1,3]) else (if i.val < 719 then [0,2,0,3,0,3,3] else [0,2,0,3,2,3,3])))) else (if i.val < 728 then (if i.val < 724 then (if i.val < 722 then (if i.val < 721 then [0,2,0,3,3,3,0] else [0,2,1,3,1,3,3]) else (if i.val < 723 then [0,2,1,3,2,3,3] else [0,2,1,3,3,3,1])) else (if i.val < 726 then (if i.val < 725 then [0,2,2,2,3,0,1] else [0,2,2,2,3,1,3]) else (if i.val < 727 then [0,2,2,2,3,3,3] else [0,2,2,3,0,1,3]))) else (if i.val < 732 then (if i.val < 730 then (if i.val < 729 then [0,2,2,3,0,2,3] else [0,2,2,3,2,0,3]) else (if i.val < 731 then [0,2,2,3,2,3,3] else [0,2,3,0,1,2,3])) else (if i.val < 734 then (if i.val < 733 then [0,2,3,0,1,3,3] else [0,2,3,0,2,1,3]) else (if i.val < 735 then [0,2,3,0,2,3,3] else [0,2,3,0,3,3,1]))))) else (if i.val < 752 then (if i.val < 744 then (if i.val < 740 then (if i.val < 738 then (if i.val < 737 then [0,2,3,0,3,3,3] else [0,2,3,1,2,0,3]) else (if i.val < 739 then [0,2,3,1,2,3,3] else [0,2,3,1,3,3,0])) else (if i.val < 742 then (if i.val < 741 then [0,2,3,1,3,3,3] else [0,2,3,2,0,1,3]) else (if i.val < 743 then [0,2,3,2,0,3,3] else [0,2,3,2,1,3,3]))) else (if i.val < 748 then (if i.val < 746 then (if i.val < 745 then [0,2,3,2,3,3,3] else [0,2,3,3,3,0,1]) else (if i.val < 747 then [0,2,3,3,3,0,3] else [0,2,3,3,3,1,3])) else (if i.val < 750 then (if i.val < 749 then [0,3,0,1,2,3,3] else [0,3,0,1,3,0,1]) else (if i.val < 751 then [0,3,0,1,3,0,2] else [0,3,0,1,3,3,3])))) else (if i.val < 760 then (if i.val < 756 then (if i.val < 754 then (if i.val < 753 then [0,3,0,2,1,3,3] else [0,3,0,2,3,2,3]) else (if i.val < 755 then [0,3,0,2,3,3,3] else [0,3,0,3,0,3,2])) else (if i.val < 758 then (if i.val < 757 then [0,3,0,3,0,3,3] else [0,3,0,3,3,1,3]) else (if i.val < 759 then [0,3,1,2,0,3,3] else [0,3,1,2,3,1,3]))) else (if i.val < 764 then (if i.val < 762 then (if i.val < 761 then [0,3,1,2,3,2,3] else [0,3,1,2,3,3,3]) else (if i.val < 763 then [0,3,1,3,1,3,3] else [0,3,1,3,3,0,3])) else (if i.val < 766 then (if i.val < 765 then [0,3,2,0,1,3,3] else [0,3,2,0,3,2,3]) else (if i.val < 767 then [0,3,2,0,3,3,3] else [0,3,2,1,3,1,3])))))))) else (if i.val < 896 then (if i.val < 832 then (if i.val < 800 then (if i.val < 784 then (if i.val < 776 then (if i.val < 772 then (if i.val < 770 then (if i.val < 769 then [0,3,2,1,3,2,3] else [0,3,2,1,3,3,3]) else (if i.val < 771 then [0,3,2,3,1,2,3] else [0,3,2,3,1,3,3])) else (if i.val < 774 then (if i.val < 773 then [0,3,2,3,2,0,3] else [0,3,2,3,2,3,3]) else (if i.val < 775 then [0,3,2,3,3,3,0] else [0,3,3,0,1,3,2]))) else (if i.val < 780 then (if i.val < 778 then (if i.val < 777 then [0,3,3,0,3,0,2] else [0,3,3,0,3,0,3]) else (if i.val < 779 then [0,3,3,1,3,1,3] else [0,3,3,3,0,1,3])) else (if i.val < 782 then (if i.val < 781 then [1,2,0,3,0,1,3] else [1,2,0,3,0,3,3]) else (if i.val < 783 then [1,2,0,3,3,3,0] else [1,2,1,3,1,3,3])))) else (if i.val < 792 then (if i.val < 788 then (if i.val < 786 then (if i.val < 785 then [1,2,1,3,3,3,1] else [1,2,2,3,0,2,3]) else (if i.val < 787 then [1,2,2,3,2,0,3] else [1,2,3,0,1,2,3])) else (if i.val < 790 then (if i.val < 789 then [1,2,3,0,1,3,3] else [1,2,3,0,2,1,3]) else (if i.val < 791 then [1,2,3,0,2,3,3] else [1,2,3,0,3,3,1]))) else (if i.val < 796 then (if i.val < 794 then (if i.val < 793 then [1,2,3,0,3,3,3] else [1,2,3,1,2,0,3]) else (if i.val < 795 then [1,2,3,1,2,3,3] else [1,2,3,1,3,3,0])) else (if i.val < 798 then (if i.val < 797 then [1,2,3,1,3,3,3] else [1,2,3,2,0,1,3]) else (if i.val < 799 then [1,2,3,2,0,3,3] else [1,2,3,2,1,3,3]))))) else (if i.val < 816 then (if i.val < 808 then (if i.val < 804 then (if i.val < 802 then (if i.val < 801 then [1,2,3,2,3,3,3] else [1,2,3,3,3,0,1]) else (if i.val < 803 then [1,2,3,3,3,0,3] else [1,2,3,3,3,1,3])) else (if i.val < 806 then (if i.val < 805 then [1,3,0,1,2,3,3] else [1,3,0,1,3,0,2]) else (if i.val < 807 then [1,3,0,1,3,3,3] else [1,3,0,2,1,3,3]))) else (if i.val < 812 then (if i.val < 810 then (if i.val < 809 then [1,3,0,2,3,2,3] else [1,3,0,2,3,3,3]) else (if i.val < 811 then [1,3,0,3,0,3,2] else [1,3,0,3,0,3,3])) else (if i.val < 814 then (if i.val < 813 then [1,3,0,3,3,1,3] else [1,3,1,2,0,3,3]) else (if i.val < 815 then [1,3,1,2,3,1,3] else [1,3,1,2,3,2,3])))) else (if i.val < 824 then (if i.val < 820 then (if i.val < 818 then (if i.val < 817 then [1,3,1,2,3,3,3] else [1,3,1,3,1,3,3]) else (if i.val < 819 then [1,3,1,3,3,0,3] else [1,3,2,0,1,3,3])) else (if i.val < 822 then (if i.val < 821 then [1,3,2,0,3,2,3] else [1,3,2,0,3,3,3]) else (if i.val < 823 then [1,3,2,1,3,1,3] else [1,3,2,1,3,2,3]))) else (if i.val < 828 then (if i.val < 826 then (if i.val < 825 then [1,3,2,1,3,3,3] else [1,3,2,3,1,3,3]) else (if i.val < 827 then [1,3,2,3,2,3,3] else [1,3,2,3,3,3,0])) else (if i.val < 830 then (if i.val < 829 then [1,3,3,0,3,0,2] else [1,3,3,0,3,0,3]) else (if i.val < 831 then [1,3,3,1,3,1,3] else [1,3,3,3,0,1,3])))))) else (if i.val < 864 then (if i.val < 848 then (if i.val < 840 then (if i.val < 836 then (if i.val < 834 then (if i.val < 833 then [2,0,3,0,3,3,3] else [2,0,3,2,3,3,3]) else (if i.val < 835 then [2,0,3,3,3,0,3] else [2,1,3,1,3,3,3])) else (if i.val < 838 then (if i.val < 837 then [2,1,3,2,3,3,3] else [2,1,3,3,3,1,3]) else (if i.val < 839 then [2,2,3,2,3,3,3] else [2,3,0,1,2,3,3]))) else (if i.val < 844 then (if i.val < 842 then (if i.val < 841 then [2,3,0,1,3,3,3] else [2,3,0,2,1,3,3]) else (if i.val < 843 then [2,3,0,2,3,3,3] else [2,3,0,3,3,1,3])) else (if i.val < 846 then (if i.val < 845 then [2,3,1,2,0,3,3] else [2,3,1,2,3,3,3]) else (if i.val < 847 then [2,3,1,3,3,0,3] else [2,3,2,0,1,3,3])))) else (if i.val < 856 then (if i.val < 852 then (if i.val < 850 then (if i.val < 849 then [2,3,2,0,3,3,3] else [2,3,2,1,3,3,3]) else (if i.val < 851 then [2,3,3,3,0,1,3] else [3,0,1,2,3,3,3])) else (if i.val < 854 then (if i.val < 853 then [3,0,2,1,3,3,3] else [3,0,2,3,2,3,3]) else (if i.val < 855 then [3,0,2,3,3,3,0] else [3,1,2,0,3,3,3]))) else (if i.val < 860 then (if i.val < 858 then (if i.val < 857 then [3,1,2,3,1,3,3] else [3,1,2,3,2,3,3]) else (if i.val < 859 then [3,2,0,1,3,3,3] else [3,2,0,3,2,3,3])) else (if i.val < 862 then (if i.val < 861 then [3,2,0,3,3,3,0] else [3,2,1,3,1,3,3]) else (if i.val < 863 then [3,2,1,3,2,3,3] else [3,2,3,1,2,3,3]))))) else (if i.val < 880 then (if i.val < 872 then (if i.val < 868 then (if i.val < 866 then (if i.val < 865 then [3,2,3,1,3,3,0] else [3,2,3,2,0,3,3]) else (if i.val < 867 then [0,1,2,0,3,0,1,3] else [0,1,2,0,3,0,3,3])) else (if i.val < 870 then (if i.val < 869 then [0,1,2,0,3,3,3,0] else [0,1,2,1,3,1,3,3]) else (if i.val < 871 then [0,1,2,1,3,3,3,1] else [0,1,2,2,3,0,2,3]))) else (if i.val < 876 then (if i.val < 874 then (if i.val < 873 then [0,1,2,2,3,2,0,3] else [0,1,2,3,0,1,2,3]) else (if i.val < 875 then [0,1,2,3,0,1,3,3] else [0,1,2,3,0,2,1,3])) else (if i.val < 878 then (if i.val < 877 then [0,1,2,3,0,2,3,3] else [0,1,2,3,0,3,3,1]) else (if i.val < 879 then [0,1,2,3,0,3,3,3] else [0,1,2,3,1,2,0,3])))) else (if i.val < 888 then (if i.val < 884 then (if i.val < 882 then (if i.val < 881 then [0,1,2,3,1,2,3,3] else [0,1,2,3,1,3,3,0]) else (if i.val < 883 then [0,1,2,3,1,3,3,3] else [0,1,2,3,2,0,1,3])) else (if i.val < 886 then (if i.val < 885 then [0,1,2,3,2,0,3,3] else [0,1,2,3,2,1,3,3]) else (if i.val < 887 then [0,1,2,3,2,3,3,3] else [0,1,2,3,3,3,0,1]))) else (if i.val < 892 then (if i.val < 890 then (if i.val < 889 then [0,1,2,3,3,3,0,3] else [0,1,2,3,3,3,1,3]) else (if i.val < 891 then [0,1,3,0,1,2,3,3] else [0,1,3,0,1,3,0,2])) else (if i.val < 894 then (if i.val < 893 then [0,1,3,0,1,3,3,3] else [0,1,3,0,2,1,3,3]) else (if i.val < 895 then [0,1,3,0,2,3,2,3] else [0,1,3,0,2,3,3,3]))))))) else (if i.val < 960 then (if i.val < 928 then (if i.val < 912 then (if i.val < 904 then (if i.val < 900 then (if i.val < 898 then (if i.val < 897 then [0,1,3,0,3,0,3,2] else [0,1,3,0,3,0,3,3]) else (if i.val < 899 then [0,1,3,0,3,3,1,3] else [0,1,3,1,2,0,3,3])) else (if i.val < 902 then (if i.val < 901 then [0,1,3,1,2,3,1,3] else [0,1,3,1,2,3,2,3]) else (if i.val < 903 then [0,1,3,1,2,3,3,3] else [0,1,3,1,3,1,3,3]))) else (if i.val < 908 then (if i.val < 906 then (if i.val < 905 then [0,1,3,1,3,3,0,3] else [0,1,3,2,0,1,3,3]) else (if i.val < 907 then [0,1,3,2,0,3,2,3] else [0,1,3,2,0,3,3,3])) else (if i.val < 910 then (if i.val < 909 then [0,1,3,2,1,3,1,3] else [0,1,3,2,1,3,2,3]) else (if i.val < 911 then [0,1,3,2,1,3,3,3] else [0,1,3,2,3,1,3,3])))) else (if i.val < 920 then (if i.val < 916 then (if i.val < 914 then (if i.val < 913 then [0,1,3,2,3,2,3,3] else [0,1,3,2,3,3,3,0]) else (if i.val < 915 then [0,1,3,3,0,3,0,2] else [0,1,3,3,0,3,0,3])) else (if i.val < 918 then (if i.val < 917 then [0,1,3,3,1,3,1,3] else [0,1,3,3,3,0,1,3]) else (if i.val < 919 then [0,2,0,3,0,3,3,3] else [0,2,0,3,2,3,3,3]))) else (if i.val < 924 then (if i.val < 922 then (if i.val < 921 then [0,2,0,3,3,3,0,3] else [0,2,1,3,1,3,3,3]) else (if i.val < 923 then [0,2,1,3,2,3,3,3] else [0,2,1,3,3,3,1,3])) else (if i.val < 926 then (if i.val < 925 then [0,2,2,3,2,3,3,3] else [0,2,3,0,1,2,3,3]) else (if i.val < 927 then [0,2,3,0,1,3,3,3] else [0,2,3,0,2,1,3,3]))))) else (if i.val < 944 then (if i.val < 936 then (if i.val < 932 then (if i.val < 930 then (if i.val < 929 then [0,2,3,0,2,3,3,3] else [0,2,3,0,3,3,1,3]) else (if i.val < 931 then [0,2,3,1,2,0,3,3] else [0,2,3,1,2,3,3,3])) else (if i.val < 934 then (if i.val < 933 then [0,2,3,1,3,3,0,3] else [0,2,3,2,0,1,3,3]) else (if i.val < 935 then [0,2,3,2,0,3,3,3] else [0,2,3,2,1,3,3,3]))) else (if i.val < 940 then (if i.val < 938 then (if i.val < 937 then [0,2,3,3,3,0,1,3] else [0,3,0,1,2,3,3,3]) else (if i.val < 939 then [0,3,0,2,1,3,3,3] else [0,3,0,2,3,2,3,3])) else (if i.val < 942 then (if i.val < 941 then [0,3,0,2,3,3,3,0] else [0,3,1,2,0,3,3,3]) else (if i.val < 943 then [0,3,1,2,3,1,3,3] else [0,3,1,2,3,2,3,3])))) else (if i.val < 952 then (if i.val < 948 then (if i.val < 946 then (if i.val < 945 then [0,3,2,0,1,3,3,3] else [0,3,2,0,3,2,3,3]) else (if i.val < 947 then [0,3,2,0,3,3,3,0] else [0,3,2,1,3,1,3,3])) else (if i.val < 950 then (if i.val < 949 then [0,3,2,1,3,2,3,3] else [0,3,2,3,1,2,3,3]) else (if i.val < 951 then [0,3,2,3,1,3,3,0] else [0,3,2,3,2,0,3,3]))) else (if i.val < 956 then (if i.val < 954 then (if i.val < 953 then [1,2,0,3,0,3,3,3] else [1,2,0,3,3,3,0,3]) else (if i.val < 955 then [1,2,1,3,1,3,3,3] else [1,2,1,3,3,3,1,3])) else (if i.val < 958 then (if i.val < 957 then [1,2,3,0,1,2,3,3] else [1,2,3,0,1,3,3,3]) else (if i.val < 959 then [1,2,3,0,2,1,3,3] else [1,2,3,0,2,3,3,3])))))) else (if i.val < 992 then (if i.val < 976 then (if i.val < 968 then (if i.val < 964 then (if i.val < 962 then (if i.val < 961 then [1,2,3,0,3,3,1,3] else [1,2,3,1,2,0,3,3]) else (if i.val < 963 then [1,2,3,1,2,3,3,3] else [1,2,3,1,3,3,0,3])) else (if i.val < 966 then (if i.val < 965 then [1,2,3,2,0,1,3,3] else [1,2,3,2,0,3,3,3]) else (if i.val < 967 then [1,2,3,2,1,3,3,3] else [1,2,3,3,3,0,1,3]))) else (if i.val < 972 then (if i.val < 970 then (if i.val < 969 then [1,3,0,1,2,3,3,3] else [1,3,0,2,1,3,3,3]) else (if i.val < 971 then [1,3,0,2,3,2,3,3] else [1,3,0,2,3,3,3,0])) else (if i.val < 974 then (if i.val < 973 then [1,3,1,2,0,3,3,3] else [1,3,1,2,3,1,3,3]) else (if i.val < 975 then [1,3,1,2,3,2,3,3] else [1,3,2,0,1,3,3,3])))) else (if i.val < 984 then (if i.val < 980 then (if i.val < 978 then (if i.val < 977 then [1,3,2,0,3,2,3,3] else [1,3,2,0,3,3,3,0]) else (if i.val < 979 then [1,3,2,1,3,1,3,3] else [1,3,2,1,3,2,3,3])) else (if i.val < 982 then (if i.val < 981 then [2,3,0,1,2,3,3,3] else [2,3,0,2,1,3,3,3]) else (if i.val < 983 then [2,3,1,2,0,3,3,3] else [2,3,2,0,1,3,3,3]))) else (if i.val < 988 then (if i.val < 986 then (if i.val < 985 then [0,1,2,0,3,0,3,3,3] else [0,1,2,0,3,3,3,0,3]) else (if i.val < 987 then [0,1,2,1,3,1,3,3,3] else [0,1,2,1,3,3,3,1,3])) else (if i.val < 990 then (if i.val < 989 then [0,1,2,3,0,1,2,3,3] else [0,1,2,3,0,1,3,3,3]) else (if i.val < 991 then [0,1,2,3,0,2,1,3,3] else [0,1,2,3,0,2,3,3,3]))))) else (if i.val < 1008 then (if i.val < 1000 then (if i.val < 996 then (if i.val < 994 then (if i.val < 993 then [0,1,2,3,0,3,3,1,3] else [0,1,2,3,1,2,0,3,3]) else (if i.val < 995 then [0,1,2,3,1,2,3,3,3] else [0,1,2,3,1,3,3,0,3])) else (if i.val < 998 then (if i.val < 997 then [0,1,2,3,2,0,1,3,3] else [0,1,2,3,2,0,3,3,3]) else (if i.val < 999 then [0,1,2,3,2,1,3,3,3] else [0,1,2,3,3,3,0,1,3]))) else (if i.val < 1004 then (if i.val < 1002 then (if i.val < 1001 then [0,1,3,0,1,2,3,3,3] else [0,1,3,0,2,1,3,3,3]) else (if i.val < 1003 then [0,1,3,0,2,3,2,3,3] else [0,1,3,0,2,3,3,3,0])) else (if i.val < 1006 then (if i.val < 1005 then [0,1,3,1,2,0,3,3,3] else [0,1,3,1,2,3,1,3,3]) else (if i.val < 1007 then [0,1,3,1,2,3,2,3,3] else [0,1,3,2,0,1,3,3,3])))) else (if i.val < 1016 then (if i.val < 1012 then (if i.val < 1010 then (if i.val < 1009 then [0,1,3,2,0,3,2,3,3] else [0,1,3,2,0,3,3,3,0]) else (if i.val < 1011 then [0,1,3,2,1,3,1,3,3] else [0,1,3,2,1,3,2,3,3])) else (if i.val < 1014 then (if i.val < 1013 then [0,2,3,0,1,2,3,3,3] else [0,2,3,0,2,1,3,3,3]) else (if i.val < 1015 then [0,2,3,1,2,0,3,3,3] else [0,2,3,2,0,1,3,3,3]))) else (if i.val < 1020 then (if i.val < 1018 then (if i.val < 1017 then [1,2,3,0,1,2,3,3,3] else [1,2,3,0,2,1,3,3,3]) else (if i.val < 1019 then [1,2,3,1,2,0,3,3,3] else [1,2,3,2,0,1,3,3,3])) else (if i.val < 1022 then (if i.val < 1021 then [0,1,2,3,0,1,2,3,3,3] else [0,1,2,3,0,2,1,3,3,3]) else (if i.val < 1023 then [0,1,2,3,1,2,0,3,3,3] else [0,1,2,3,2,0,1,3,3,3]))))))))))
private def alphaCayley : FiniteCayleyCertificate (fun j => (alphaGenerators j, alphaImages j)) 1024 where
  elements := (fun i => (alphaSource i, alphaTarget i))
  identity := 0
  identity_eq := by decide +kernel
  next i j := (alphaNextTable i)[j.val]!
  next_eq := (Fin.addCases (m := 512) (n := 512) (Fin.addCases (m := 256) (n := 256) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)))) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))))) (Fin.addCases (m := 256) (n := 256) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)))) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))))))
  words i := alphaWordTable i
  words_eq := (Fin.addCases (m := 512) (n := 512) (Fin.addCases (m := 256) (n := 256) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)))) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))))) (Fin.addCases (m := 256) (n := 256) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)))) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))))))

def alphaCertificate : FiniteHomCertificate alphaGenerators alphaImages 1024 where
  cayley := alphaCayley
  first_kernel := (Fin.addCases (m := 512) (n := 512) (Fin.addCases (m := 256) (n := 256) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)))) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))))) (Fin.addCases (m := 256) (n := 256) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)))) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))))))

private def betaSourceLiteral0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral3 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral4 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral5 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral6 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral7 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral8 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral9 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral10 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral11 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral12 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral13 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral14 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral15 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral16 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral17 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral18 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral19 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral20 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral21 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral22 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral23 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral24 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral25 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral26 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral27 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral28 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral29 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral30 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral31 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral32 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral33 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral34 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral35 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral36 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral37 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral38 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral39 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral40 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral41 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral42 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral43 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral44 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral45 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral46 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral47 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral48 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral49 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral50 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral51 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral52 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral53 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral54 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral55 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral56 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral57 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral58 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral59 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral60 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral61 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral62 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral63 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral64 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral65 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral66 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral67 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral68 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral69 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral70 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral71 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral72 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral73 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral74 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral75 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral76 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral77 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral78 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral79 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral80 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral81 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral82 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral83 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral84 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral85 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral86 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral87 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral88 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral89 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral90 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral91 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral92 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral93 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral94 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral95 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral96 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral97 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral98 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral99 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral100 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral101 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral102 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral103 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral104 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral105 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral106 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral107 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral108 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral109 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral110 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral111 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral112 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral113 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral114 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral115 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral116 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral117 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral118 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral119 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral120 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral121 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral122 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral123 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral124 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral125 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral126 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral127 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral128 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral129 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral130 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral131 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral132 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral133 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral134 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral135 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral136 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral137 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral138 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral139 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral140 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral141 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral142 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral143 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral144 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral145 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral146 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral147 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral148 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral149 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral150 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral151 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral152 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral153 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral154 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral155 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral156 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral157 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral158 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral159 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral160 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral161 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral162 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral163 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral164 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral165 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral166 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral167 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral168 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral169 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral170 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral171 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral172 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral173 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral174 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral175 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral176 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral177 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral178 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral179 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral180 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral181 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral182 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral183 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral184 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral185 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral186 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral187 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral188 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral189 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral190 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral191 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral192 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral193 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral194 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral195 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral196 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral197 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral198 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral199 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral200 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral201 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral202 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral203 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral204 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral205 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral206 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral207 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral208 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral209 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral210 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral211 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral212 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral213 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral214 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral215 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral216 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral217 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral218 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral219 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral220 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral221 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral222 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral223 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral224 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral225 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral226 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral227 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral228 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral229 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral230 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral231 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral232 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral233 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral234 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral235 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral236 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral237 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral238 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral239 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral240 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral241 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral242 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral243 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral244 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral245 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral246 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral247 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral248 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral249 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral250 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral251 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral252 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral253 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral254 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSourceLiteral255 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaSource (i : Fin 256) : Equiv.Perm (Fin 16) :=
  (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then betaSourceLiteral0 else betaSourceLiteral1) else (if i.val < 3 then betaSourceLiteral2 else betaSourceLiteral3)) else (if i.val < 6 then (if i.val < 5 then betaSourceLiteral4 else betaSourceLiteral5) else (if i.val < 7 then betaSourceLiteral6 else betaSourceLiteral7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then betaSourceLiteral8 else betaSourceLiteral9) else (if i.val < 11 then betaSourceLiteral10 else betaSourceLiteral11)) else (if i.val < 14 then (if i.val < 13 then betaSourceLiteral12 else betaSourceLiteral13) else (if i.val < 15 then betaSourceLiteral14 else betaSourceLiteral15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then betaSourceLiteral16 else betaSourceLiteral17) else (if i.val < 19 then betaSourceLiteral18 else betaSourceLiteral19)) else (if i.val < 22 then (if i.val < 21 then betaSourceLiteral20 else betaSourceLiteral21) else (if i.val < 23 then betaSourceLiteral22 else betaSourceLiteral23))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then betaSourceLiteral24 else betaSourceLiteral25) else (if i.val < 27 then betaSourceLiteral26 else betaSourceLiteral27)) else (if i.val < 30 then (if i.val < 29 then betaSourceLiteral28 else betaSourceLiteral29) else (if i.val < 31 then betaSourceLiteral30 else betaSourceLiteral31))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then betaSourceLiteral32 else betaSourceLiteral33) else (if i.val < 35 then betaSourceLiteral34 else betaSourceLiteral35)) else (if i.val < 38 then (if i.val < 37 then betaSourceLiteral36 else betaSourceLiteral37) else (if i.val < 39 then betaSourceLiteral38 else betaSourceLiteral39))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then betaSourceLiteral40 else betaSourceLiteral41) else (if i.val < 43 then betaSourceLiteral42 else betaSourceLiteral43)) else (if i.val < 46 then (if i.val < 45 then betaSourceLiteral44 else betaSourceLiteral45) else (if i.val < 47 then betaSourceLiteral46 else betaSourceLiteral47)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then betaSourceLiteral48 else betaSourceLiteral49) else (if i.val < 51 then betaSourceLiteral50 else betaSourceLiteral51)) else (if i.val < 54 then (if i.val < 53 then betaSourceLiteral52 else betaSourceLiteral53) else (if i.val < 55 then betaSourceLiteral54 else betaSourceLiteral55))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then betaSourceLiteral56 else betaSourceLiteral57) else (if i.val < 59 then betaSourceLiteral58 else betaSourceLiteral59)) else (if i.val < 62 then (if i.val < 61 then betaSourceLiteral60 else betaSourceLiteral61) else (if i.val < 63 then betaSourceLiteral62 else betaSourceLiteral63)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then betaSourceLiteral64 else betaSourceLiteral65) else (if i.val < 67 then betaSourceLiteral66 else betaSourceLiteral67)) else (if i.val < 70 then (if i.val < 69 then betaSourceLiteral68 else betaSourceLiteral69) else (if i.val < 71 then betaSourceLiteral70 else betaSourceLiteral71))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then betaSourceLiteral72 else betaSourceLiteral73) else (if i.val < 75 then betaSourceLiteral74 else betaSourceLiteral75)) else (if i.val < 78 then (if i.val < 77 then betaSourceLiteral76 else betaSourceLiteral77) else (if i.val < 79 then betaSourceLiteral78 else betaSourceLiteral79)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then betaSourceLiteral80 else betaSourceLiteral81) else (if i.val < 83 then betaSourceLiteral82 else betaSourceLiteral83)) else (if i.val < 86 then (if i.val < 85 then betaSourceLiteral84 else betaSourceLiteral85) else (if i.val < 87 then betaSourceLiteral86 else betaSourceLiteral87))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then betaSourceLiteral88 else betaSourceLiteral89) else (if i.val < 91 then betaSourceLiteral90 else betaSourceLiteral91)) else (if i.val < 94 then (if i.val < 93 then betaSourceLiteral92 else betaSourceLiteral93) else (if i.val < 95 then betaSourceLiteral94 else betaSourceLiteral95))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then betaSourceLiteral96 else betaSourceLiteral97) else (if i.val < 99 then betaSourceLiteral98 else betaSourceLiteral99)) else (if i.val < 102 then (if i.val < 101 then betaSourceLiteral100 else betaSourceLiteral101) else (if i.val < 103 then betaSourceLiteral102 else betaSourceLiteral103))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then betaSourceLiteral104 else betaSourceLiteral105) else (if i.val < 107 then betaSourceLiteral106 else betaSourceLiteral107)) else (if i.val < 110 then (if i.val < 109 then betaSourceLiteral108 else betaSourceLiteral109) else (if i.val < 111 then betaSourceLiteral110 else betaSourceLiteral111)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then betaSourceLiteral112 else betaSourceLiteral113) else (if i.val < 115 then betaSourceLiteral114 else betaSourceLiteral115)) else (if i.val < 118 then (if i.val < 117 then betaSourceLiteral116 else betaSourceLiteral117) else (if i.val < 119 then betaSourceLiteral118 else betaSourceLiteral119))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then betaSourceLiteral120 else betaSourceLiteral121) else (if i.val < 123 then betaSourceLiteral122 else betaSourceLiteral123)) else (if i.val < 126 then (if i.val < 125 then betaSourceLiteral124 else betaSourceLiteral125) else (if i.val < 127 then betaSourceLiteral126 else betaSourceLiteral127))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then betaSourceLiteral128 else betaSourceLiteral129) else (if i.val < 131 then betaSourceLiteral130 else betaSourceLiteral131)) else (if i.val < 134 then (if i.val < 133 then betaSourceLiteral132 else betaSourceLiteral133) else (if i.val < 135 then betaSourceLiteral134 else betaSourceLiteral135))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then betaSourceLiteral136 else betaSourceLiteral137) else (if i.val < 139 then betaSourceLiteral138 else betaSourceLiteral139)) else (if i.val < 142 then (if i.val < 141 then betaSourceLiteral140 else betaSourceLiteral141) else (if i.val < 143 then betaSourceLiteral142 else betaSourceLiteral143)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then betaSourceLiteral144 else betaSourceLiteral145) else (if i.val < 147 then betaSourceLiteral146 else betaSourceLiteral147)) else (if i.val < 150 then (if i.val < 149 then betaSourceLiteral148 else betaSourceLiteral149) else (if i.val < 151 then betaSourceLiteral150 else betaSourceLiteral151))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then betaSourceLiteral152 else betaSourceLiteral153) else (if i.val < 155 then betaSourceLiteral154 else betaSourceLiteral155)) else (if i.val < 158 then (if i.val < 157 then betaSourceLiteral156 else betaSourceLiteral157) else (if i.val < 159 then betaSourceLiteral158 else betaSourceLiteral159))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then betaSourceLiteral160 else betaSourceLiteral161) else (if i.val < 163 then betaSourceLiteral162 else betaSourceLiteral163)) else (if i.val < 166 then (if i.val < 165 then betaSourceLiteral164 else betaSourceLiteral165) else (if i.val < 167 then betaSourceLiteral166 else betaSourceLiteral167))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then betaSourceLiteral168 else betaSourceLiteral169) else (if i.val < 171 then betaSourceLiteral170 else betaSourceLiteral171)) else (if i.val < 174 then (if i.val < 173 then betaSourceLiteral172 else betaSourceLiteral173) else (if i.val < 175 then betaSourceLiteral174 else betaSourceLiteral175)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then betaSourceLiteral176 else betaSourceLiteral177) else (if i.val < 179 then betaSourceLiteral178 else betaSourceLiteral179)) else (if i.val < 182 then (if i.val < 181 then betaSourceLiteral180 else betaSourceLiteral181) else (if i.val < 183 then betaSourceLiteral182 else betaSourceLiteral183))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then betaSourceLiteral184 else betaSourceLiteral185) else (if i.val < 187 then betaSourceLiteral186 else betaSourceLiteral187)) else (if i.val < 190 then (if i.val < 189 then betaSourceLiteral188 else betaSourceLiteral189) else (if i.val < 191 then betaSourceLiteral190 else betaSourceLiteral191)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then betaSourceLiteral192 else betaSourceLiteral193) else (if i.val < 195 then betaSourceLiteral194 else betaSourceLiteral195)) else (if i.val < 198 then (if i.val < 197 then betaSourceLiteral196 else betaSourceLiteral197) else (if i.val < 199 then betaSourceLiteral198 else betaSourceLiteral199))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then betaSourceLiteral200 else betaSourceLiteral201) else (if i.val < 203 then betaSourceLiteral202 else betaSourceLiteral203)) else (if i.val < 206 then (if i.val < 205 then betaSourceLiteral204 else betaSourceLiteral205) else (if i.val < 207 then betaSourceLiteral206 else betaSourceLiteral207)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then betaSourceLiteral208 else betaSourceLiteral209) else (if i.val < 211 then betaSourceLiteral210 else betaSourceLiteral211)) else (if i.val < 214 then (if i.val < 213 then betaSourceLiteral212 else betaSourceLiteral213) else (if i.val < 215 then betaSourceLiteral214 else betaSourceLiteral215))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then betaSourceLiteral216 else betaSourceLiteral217) else (if i.val < 219 then betaSourceLiteral218 else betaSourceLiteral219)) else (if i.val < 222 then (if i.val < 221 then betaSourceLiteral220 else betaSourceLiteral221) else (if i.val < 223 then betaSourceLiteral222 else betaSourceLiteral223))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then betaSourceLiteral224 else betaSourceLiteral225) else (if i.val < 227 then betaSourceLiteral226 else betaSourceLiteral227)) else (if i.val < 230 then (if i.val < 229 then betaSourceLiteral228 else betaSourceLiteral229) else (if i.val < 231 then betaSourceLiteral230 else betaSourceLiteral231))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then betaSourceLiteral232 else betaSourceLiteral233) else (if i.val < 235 then betaSourceLiteral234 else betaSourceLiteral235)) else (if i.val < 238 then (if i.val < 237 then betaSourceLiteral236 else betaSourceLiteral237) else (if i.val < 239 then betaSourceLiteral238 else betaSourceLiteral239)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then betaSourceLiteral240 else betaSourceLiteral241) else (if i.val < 243 then betaSourceLiteral242 else betaSourceLiteral243)) else (if i.val < 246 then (if i.val < 245 then betaSourceLiteral244 else betaSourceLiteral245) else (if i.val < 247 then betaSourceLiteral246 else betaSourceLiteral247))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then betaSourceLiteral248 else betaSourceLiteral249) else (if i.val < 251 then betaSourceLiteral250 else betaSourceLiteral251)) else (if i.val < 254 then (if i.val < 253 then betaSourceLiteral252 else betaSourceLiteral253) else (if i.val < 255 then betaSourceLiteral254 else betaSourceLiteral255))))))))

private def betaTargetLiteral0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral3 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral4 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral5 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral6 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral7 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral8 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral9 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral10 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral11 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral12 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral13 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral14 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral15 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral16 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral17 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral18 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral19 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral20 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral21 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral22 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral23 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral24 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral25 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral26 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral27 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral28 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral29 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral30 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral31 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral32 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral33 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral34 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral35 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral36 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral37 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral38 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral39 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral40 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral41 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral42 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral43 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral44 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral45 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral46 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral47 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral48 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral49 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral50 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral51 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral52 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral53 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral54 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral55 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral56 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral57 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral58 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral59 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral60 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral61 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral62 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral63 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral64 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral65 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral66 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral67 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral68 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral69 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral70 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral71 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral72 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral73 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral74 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral75 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral76 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral77 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral78 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral79 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral80 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral81 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral82 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral83 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral84 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral85 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral86 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral87 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral88 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral89 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral90 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral91 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral92 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral93 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral94 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral95 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral96 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral97 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral98 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral99 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral100 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral101 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral102 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral103 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral104 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral105 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral106 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral107 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral108 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral109 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral110 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral111 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral112 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral113 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral114 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral115 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral116 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral117 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral118 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral119 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral120 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral121 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral122 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral123 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral124 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral125 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral126 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral127 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral128 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral129 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral130 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral131 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral132 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral133 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral134 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral135 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral136 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral137 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral138 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral139 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral140 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral141 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral142 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral143 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral144 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral145 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral146 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral147 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral148 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral149 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral150 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral151 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral152 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral153 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral154 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral155 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral156 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral157 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral158 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral159 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral160 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral161 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral162 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral163 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral164 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral165 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral166 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral167 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral168 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral169 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral170 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral171 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral172 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral173 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral174 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral175 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral176 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral177 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral178 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral179 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral180 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral181 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral182 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral183 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral184 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral185 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral186 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral187 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral188 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral189 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral190 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral191 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral192 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral193 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral194 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral195 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral196 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral197 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral198 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral199 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral200 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral201 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral202 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral203 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral204 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral205 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral206 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral207 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral208 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral209 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral210 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral211 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral212 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral213 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral214 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral215 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral216 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral217 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral218 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral219 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral220 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral221 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral222 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral223 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral224 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral225 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral226 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral227 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral228 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral229 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral230 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral231 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral232 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral233 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral234 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral235 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral236 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral237 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral238 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral239 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral240 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral241 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral242 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral243 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral244 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral245 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral246 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral247 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral248 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral249 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral250 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral251 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral252 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral253 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral254 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTargetLiteral255 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def betaTarget (i : Fin 256) : Equiv.Perm (Fin 16) :=
  (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then betaTargetLiteral0 else betaTargetLiteral1) else (if i.val < 3 then betaTargetLiteral2 else betaTargetLiteral3)) else (if i.val < 6 then (if i.val < 5 then betaTargetLiteral4 else betaTargetLiteral5) else (if i.val < 7 then betaTargetLiteral6 else betaTargetLiteral7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then betaTargetLiteral8 else betaTargetLiteral9) else (if i.val < 11 then betaTargetLiteral10 else betaTargetLiteral11)) else (if i.val < 14 then (if i.val < 13 then betaTargetLiteral12 else betaTargetLiteral13) else (if i.val < 15 then betaTargetLiteral14 else betaTargetLiteral15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then betaTargetLiteral16 else betaTargetLiteral17) else (if i.val < 19 then betaTargetLiteral18 else betaTargetLiteral19)) else (if i.val < 22 then (if i.val < 21 then betaTargetLiteral20 else betaTargetLiteral21) else (if i.val < 23 then betaTargetLiteral22 else betaTargetLiteral23))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then betaTargetLiteral24 else betaTargetLiteral25) else (if i.val < 27 then betaTargetLiteral26 else betaTargetLiteral27)) else (if i.val < 30 then (if i.val < 29 then betaTargetLiteral28 else betaTargetLiteral29) else (if i.val < 31 then betaTargetLiteral30 else betaTargetLiteral31))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then betaTargetLiteral32 else betaTargetLiteral33) else (if i.val < 35 then betaTargetLiteral34 else betaTargetLiteral35)) else (if i.val < 38 then (if i.val < 37 then betaTargetLiteral36 else betaTargetLiteral37) else (if i.val < 39 then betaTargetLiteral38 else betaTargetLiteral39))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then betaTargetLiteral40 else betaTargetLiteral41) else (if i.val < 43 then betaTargetLiteral42 else betaTargetLiteral43)) else (if i.val < 46 then (if i.val < 45 then betaTargetLiteral44 else betaTargetLiteral45) else (if i.val < 47 then betaTargetLiteral46 else betaTargetLiteral47)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then betaTargetLiteral48 else betaTargetLiteral49) else (if i.val < 51 then betaTargetLiteral50 else betaTargetLiteral51)) else (if i.val < 54 then (if i.val < 53 then betaTargetLiteral52 else betaTargetLiteral53) else (if i.val < 55 then betaTargetLiteral54 else betaTargetLiteral55))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then betaTargetLiteral56 else betaTargetLiteral57) else (if i.val < 59 then betaTargetLiteral58 else betaTargetLiteral59)) else (if i.val < 62 then (if i.val < 61 then betaTargetLiteral60 else betaTargetLiteral61) else (if i.val < 63 then betaTargetLiteral62 else betaTargetLiteral63)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then betaTargetLiteral64 else betaTargetLiteral65) else (if i.val < 67 then betaTargetLiteral66 else betaTargetLiteral67)) else (if i.val < 70 then (if i.val < 69 then betaTargetLiteral68 else betaTargetLiteral69) else (if i.val < 71 then betaTargetLiteral70 else betaTargetLiteral71))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then betaTargetLiteral72 else betaTargetLiteral73) else (if i.val < 75 then betaTargetLiteral74 else betaTargetLiteral75)) else (if i.val < 78 then (if i.val < 77 then betaTargetLiteral76 else betaTargetLiteral77) else (if i.val < 79 then betaTargetLiteral78 else betaTargetLiteral79)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then betaTargetLiteral80 else betaTargetLiteral81) else (if i.val < 83 then betaTargetLiteral82 else betaTargetLiteral83)) else (if i.val < 86 then (if i.val < 85 then betaTargetLiteral84 else betaTargetLiteral85) else (if i.val < 87 then betaTargetLiteral86 else betaTargetLiteral87))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then betaTargetLiteral88 else betaTargetLiteral89) else (if i.val < 91 then betaTargetLiteral90 else betaTargetLiteral91)) else (if i.val < 94 then (if i.val < 93 then betaTargetLiteral92 else betaTargetLiteral93) else (if i.val < 95 then betaTargetLiteral94 else betaTargetLiteral95))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then betaTargetLiteral96 else betaTargetLiteral97) else (if i.val < 99 then betaTargetLiteral98 else betaTargetLiteral99)) else (if i.val < 102 then (if i.val < 101 then betaTargetLiteral100 else betaTargetLiteral101) else (if i.val < 103 then betaTargetLiteral102 else betaTargetLiteral103))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then betaTargetLiteral104 else betaTargetLiteral105) else (if i.val < 107 then betaTargetLiteral106 else betaTargetLiteral107)) else (if i.val < 110 then (if i.val < 109 then betaTargetLiteral108 else betaTargetLiteral109) else (if i.val < 111 then betaTargetLiteral110 else betaTargetLiteral111)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then betaTargetLiteral112 else betaTargetLiteral113) else (if i.val < 115 then betaTargetLiteral114 else betaTargetLiteral115)) else (if i.val < 118 then (if i.val < 117 then betaTargetLiteral116 else betaTargetLiteral117) else (if i.val < 119 then betaTargetLiteral118 else betaTargetLiteral119))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then betaTargetLiteral120 else betaTargetLiteral121) else (if i.val < 123 then betaTargetLiteral122 else betaTargetLiteral123)) else (if i.val < 126 then (if i.val < 125 then betaTargetLiteral124 else betaTargetLiteral125) else (if i.val < 127 then betaTargetLiteral126 else betaTargetLiteral127))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then betaTargetLiteral128 else betaTargetLiteral129) else (if i.val < 131 then betaTargetLiteral130 else betaTargetLiteral131)) else (if i.val < 134 then (if i.val < 133 then betaTargetLiteral132 else betaTargetLiteral133) else (if i.val < 135 then betaTargetLiteral134 else betaTargetLiteral135))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then betaTargetLiteral136 else betaTargetLiteral137) else (if i.val < 139 then betaTargetLiteral138 else betaTargetLiteral139)) else (if i.val < 142 then (if i.val < 141 then betaTargetLiteral140 else betaTargetLiteral141) else (if i.val < 143 then betaTargetLiteral142 else betaTargetLiteral143)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then betaTargetLiteral144 else betaTargetLiteral145) else (if i.val < 147 then betaTargetLiteral146 else betaTargetLiteral147)) else (if i.val < 150 then (if i.val < 149 then betaTargetLiteral148 else betaTargetLiteral149) else (if i.val < 151 then betaTargetLiteral150 else betaTargetLiteral151))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then betaTargetLiteral152 else betaTargetLiteral153) else (if i.val < 155 then betaTargetLiteral154 else betaTargetLiteral155)) else (if i.val < 158 then (if i.val < 157 then betaTargetLiteral156 else betaTargetLiteral157) else (if i.val < 159 then betaTargetLiteral158 else betaTargetLiteral159))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then betaTargetLiteral160 else betaTargetLiteral161) else (if i.val < 163 then betaTargetLiteral162 else betaTargetLiteral163)) else (if i.val < 166 then (if i.val < 165 then betaTargetLiteral164 else betaTargetLiteral165) else (if i.val < 167 then betaTargetLiteral166 else betaTargetLiteral167))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then betaTargetLiteral168 else betaTargetLiteral169) else (if i.val < 171 then betaTargetLiteral170 else betaTargetLiteral171)) else (if i.val < 174 then (if i.val < 173 then betaTargetLiteral172 else betaTargetLiteral173) else (if i.val < 175 then betaTargetLiteral174 else betaTargetLiteral175)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then betaTargetLiteral176 else betaTargetLiteral177) else (if i.val < 179 then betaTargetLiteral178 else betaTargetLiteral179)) else (if i.val < 182 then (if i.val < 181 then betaTargetLiteral180 else betaTargetLiteral181) else (if i.val < 183 then betaTargetLiteral182 else betaTargetLiteral183))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then betaTargetLiteral184 else betaTargetLiteral185) else (if i.val < 187 then betaTargetLiteral186 else betaTargetLiteral187)) else (if i.val < 190 then (if i.val < 189 then betaTargetLiteral188 else betaTargetLiteral189) else (if i.val < 191 then betaTargetLiteral190 else betaTargetLiteral191)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then betaTargetLiteral192 else betaTargetLiteral193) else (if i.val < 195 then betaTargetLiteral194 else betaTargetLiteral195)) else (if i.val < 198 then (if i.val < 197 then betaTargetLiteral196 else betaTargetLiteral197) else (if i.val < 199 then betaTargetLiteral198 else betaTargetLiteral199))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then betaTargetLiteral200 else betaTargetLiteral201) else (if i.val < 203 then betaTargetLiteral202 else betaTargetLiteral203)) else (if i.val < 206 then (if i.val < 205 then betaTargetLiteral204 else betaTargetLiteral205) else (if i.val < 207 then betaTargetLiteral206 else betaTargetLiteral207)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then betaTargetLiteral208 else betaTargetLiteral209) else (if i.val < 211 then betaTargetLiteral210 else betaTargetLiteral211)) else (if i.val < 214 then (if i.val < 213 then betaTargetLiteral212 else betaTargetLiteral213) else (if i.val < 215 then betaTargetLiteral214 else betaTargetLiteral215))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then betaTargetLiteral216 else betaTargetLiteral217) else (if i.val < 219 then betaTargetLiteral218 else betaTargetLiteral219)) else (if i.val < 222 then (if i.val < 221 then betaTargetLiteral220 else betaTargetLiteral221) else (if i.val < 223 then betaTargetLiteral222 else betaTargetLiteral223))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then betaTargetLiteral224 else betaTargetLiteral225) else (if i.val < 227 then betaTargetLiteral226 else betaTargetLiteral227)) else (if i.val < 230 then (if i.val < 229 then betaTargetLiteral228 else betaTargetLiteral229) else (if i.val < 231 then betaTargetLiteral230 else betaTargetLiteral231))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then betaTargetLiteral232 else betaTargetLiteral233) else (if i.val < 235 then betaTargetLiteral234 else betaTargetLiteral235)) else (if i.val < 238 then (if i.val < 237 then betaTargetLiteral236 else betaTargetLiteral237) else (if i.val < 239 then betaTargetLiteral238 else betaTargetLiteral239)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then betaTargetLiteral240 else betaTargetLiteral241) else (if i.val < 243 then betaTargetLiteral242 else betaTargetLiteral243)) else (if i.val < 246 then (if i.val < 245 then betaTargetLiteral244 else betaTargetLiteral245) else (if i.val < 247 then betaTargetLiteral246 else betaTargetLiteral247))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then betaTargetLiteral248 else betaTargetLiteral249) else (if i.val < 251 then betaTargetLiteral250 else betaTargetLiteral251)) else (if i.val < 254 then (if i.val < 253 then betaTargetLiteral252 else betaTargetLiteral253) else (if i.val < 255 then betaTargetLiteral254 else betaTargetLiteral255))))))))

def betaGenerators (j : Fin 4) := betaSource (#[1,2,3,4][j.val]!)
def betaImages (j : Fin 4) := betaTarget (#[1,2,3,4][j.val]!)
private def betaNextTable (i : Fin 256) : Array (Fin 256) :=
  (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3,4] else #[5,6,7,8]) else (if i.val < 3 then #[9,0,10,11] else #[12,10,0,13])) else (if i.val < 6 then (if i.val < 5 then #[14,11,13,0] else #[15,16,17,18]) else (if i.val < 7 then #[19,1,20,21] else #[22,20,1,23]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[24,21,23,1] else #[16,25,26,27]) else (if i.val < 11 then #[28,3,2,29] else #[30,4,29,2])) else (if i.val < 14 then (if i.val < 13 then #[17,31,32,33] else #[34,29,4,3]) else (if i.val < 15 then #[18,35,36,37] else #[0,38,39,40])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[41,5,42,43] else #[44,42,5,45]) else (if i.val < 19 then #[46,43,45,5] else #[38,47,48,49])) else (if i.val < 22 then (if i.val < 21 then #[50,7,6,51] else #[52,8,51,6]) else (if i.val < 23 then #[39,53,54,55] else #[56,51,8,7]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[40,57,58,59] else #[47,9,60,61]) else (if i.val < 27 then #[53,60,9,62] else #[57,61,62,9])) else (if i.val < 30 then (if i.val < 29 then #[42,63,64,65] else #[66,13,11,10]) else (if i.val < 31 then #[43,67,68,69] else #[48,12,70,71]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[54,70,12,72] else #[58,71,72,12]) else (if i.val < 35 then #[45,73,74,75] else #[49,14,76,77])) else (if i.val < 38 then (if i.val < 37 then #[55,76,14,78] else #[59,77,78,14]) else (if i.val < 39 then #[79,15,80,81] else #[82,80,15,83]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[84,81,83,15] else #[2,85,86,87]) else (if i.val < 43 then #[88,17,16,89] else #[90,18,89,16])) else (if i.val < 46 then (if i.val < 45 then #[3,91,92,93] else #[94,89,18,17]) else (if i.val < 47 then #[4,95,96,97] else #[85,19,98,99])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[91,98,19,100] else #[95,99,100,19]) else (if i.val < 51 then #[80,101,102,103] else #[104,23,21,20])) else (if i.val < 54 then (if i.val < 53 then #[81,105,106,107] else #[86,22,108,109]) else (if i.val < 55 then #[92,108,22,110] else #[96,109,110,22]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[83,111,112,113] else #[87,24,114,115]) else (if i.val < 59 then #[93,114,24,116] else #[97,115,116,24])) else (if i.val < 62 then (if i.val < 61 then #[101,26,25,117] else #[105,27,117,25]) else (if i.val < 63 then #[111,117,27,26] else #[98,28,118,119])))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then #[108,118,28,120] else #[114,119,120,28]) else (if i.val < 67 then #[89,121,122,123] else #[99,30,124,125])) else (if i.val < 70 then (if i.val < 69 then #[109,124,30,126] else #[115,125,126,30]) else (if i.val < 71 then #[102,32,31,127] else #[106,33,127,31]))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then #[112,127,33,32] else #[100,34,128,129]) else (if i.val < 75 then #[110,128,34,130] else #[116,129,130,34])) else (if i.val < 78 then (if i.val < 77 then #[103,36,35,131] else #[107,37,131,35]) else (if i.val < 79 then #[113,131,37,36] else #[6,132,133,134])))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then #[135,39,38,136] else #[137,40,136,38]) else (if i.val < 83 then #[7,138,139,140] else #[141,136,40,39])) else (if i.val < 86 then (if i.val < 85 then #[8,142,143,144] else #[132,41,145,146]) else (if i.val < 87 then #[138,145,41,147] else #[142,146,147,41]))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then #[10,148,149,150] else #[151,45,43,42]) else (if i.val < 91 then #[11,152,153,154] else #[133,44,155,156])) else (if i.val < 94 then (if i.val < 93 then #[139,155,44,157] else #[143,156,157,44]) else (if i.val < 95 then #[13,158,159,160] else #[134,46,161,162]))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then #[140,161,46,163] else #[144,162,163,46]) else (if i.val < 99 then #[148,48,47,164] else #[152,49,164,47])) else (if i.val < 102 then (if i.val < 101 then #[158,164,49,48] else #[145,50,165,166]) else (if i.val < 103 then #[155,165,50,167] else #[161,166,167,50]))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then #[136,168,169,170] else #[146,52,171,172]) else (if i.val < 107 then #[156,171,52,173] else #[162,172,173,52])) else (if i.val < 110 then (if i.val < 109 then #[149,54,53,174] else #[153,55,174,53]) else (if i.val < 111 then #[159,174,55,54] else #[147,56,175,176])))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then #[157,175,56,177] else #[163,176,177,56]) else (if i.val < 115 then #[150,58,57,178] else #[154,59,178,57])) else (if i.val < 118 then (if i.val < 117 then #[160,178,59,58] else #[168,62,61,60]) else (if i.val < 119 then #[165,64,63,179] else #[171,65,179,63]))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then #[175,179,65,64] else #[164,66,180,181]) else (if i.val < 123 then #[174,180,66,182] else #[178,181,182,66])) else (if i.val < 126 then (if i.val < 125 then #[166,68,67,183] else #[172,69,183,67]) else (if i.val < 127 then #[176,183,69,68] else #[169,72,71,70]))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then #[167,74,73,184] else #[173,75,184,73]) else (if i.val < 131 then #[177,184,75,74] else #[170,78,77,76])) else (if i.val < 134 then (if i.val < 133 then #[25,79,185,186] else #[31,185,79,187]) else (if i.val < 135 then #[35,186,187,79] else #[20,188,189,190]))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then #[191,83,81,80] else #[21,192,193,194]) else (if i.val < 139 then #[26,82,195,196] else #[32,195,82,197])) else (if i.val < 142 then (if i.val < 141 then #[36,196,197,82] else #[23,198,199,200]) else (if i.val < 143 then #[27,84,201,202] else #[33,201,84,203])))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then #[37,202,203,84] else #[188,86,85,204]) else (if i.val < 147 then #[192,87,204,85] else #[198,204,87,86])) else (if i.val < 150 then (if i.val < 149 then #[185,88,205,206] else #[195,205,88,207]) else (if i.val < 151 then #[201,206,207,88] else #[29,208,209,210]))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then #[186,90,211,212] else #[196,211,90,213]) else (if i.val < 155 then #[202,212,213,90] else #[189,92,91,214])) else (if i.val < 158 then (if i.val < 157 then #[193,93,214,91] else #[199,214,93,92]) else (if i.val < 159 then #[187,94,215,216] else #[197,215,94,217]))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then #[203,216,217,94] else #[190,96,95,218]) else (if i.val < 163 then #[194,97,218,95] else #[200,218,97,96])) else (if i.val < 166 then (if i.val < 165 then #[208,100,99,98] else #[205,102,101,219]) else (if i.val < 167 then #[211,103,219,101] else #[215,219,103,102]))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then #[204,104,220,221] else #[214,220,104,222]) else (if i.val < 171 then #[218,221,222,104] else #[206,106,105,223])) else (if i.val < 174 then (if i.val < 173 then #[212,107,223,105] else #[216,223,107,106]) else (if i.val < 175 then #[209,110,109,108] else #[207,112,111,224])))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then #[213,113,224,111] else #[217,224,113,112]) else (if i.val < 179 then #[210,116,115,114] else #[220,120,119,118])) else (if i.val < 182 then (if i.val < 181 then #[219,122,121,225] else #[223,123,225,121]) else (if i.val < 183 then #[224,225,123,122] else #[221,126,125,124]))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then #[222,130,129,128] else #[63,133,132,226]) else (if i.val < 187 then #[67,134,226,132] else #[73,226,134,133])) else (if i.val < 190 then (if i.val < 189 then #[60,135,227,228] else #[70,227,135,229]) else (if i.val < 191 then #[76,228,229,135] else #[51,230,231,232])))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then #[61,137,233,234] else #[71,233,137,235]) else (if i.val < 195 then #[77,234,235,137] else #[64,139,138,236])) else (if i.val < 198 then (if i.val < 197 then #[68,140,236,138] else #[74,236,140,139]) else (if i.val < 199 then #[62,141,237,238] else #[72,237,141,239]))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then #[78,238,239,141] else #[65,143,142,240]) else (if i.val < 203 then #[69,144,240,142] else #[75,240,144,143])) else (if i.val < 206 then (if i.val < 205 then #[230,147,146,145] else #[227,149,148,241]) else (if i.val < 207 then #[233,150,241,148] else #[237,241,150,149])))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then #[226,151,242,243] else #[236,242,151,244]) else (if i.val < 211 then #[240,243,244,151] else #[228,153,152,245])) else (if i.val < 214 then (if i.val < 213 then #[234,154,245,152] else #[238,245,154,153]) else (if i.val < 215 then #[231,157,156,155] else #[229,159,158,246]))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then #[235,160,246,158] else #[239,246,160,159]) else (if i.val < 219 then #[232,163,162,161] else #[242,167,166,165])) else (if i.val < 222 then (if i.val < 221 then #[241,169,168,247] else #[245,170,247,168]) else (if i.val < 223 then #[246,247,170,169] else #[243,173,172,171]))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then #[244,177,176,175] else #[247,182,181,180]) else (if i.val < 227 then #[121,187,186,185] else #[118,189,188,248])) else (if i.val < 230 then (if i.val < 229 then #[124,190,248,188] else #[128,248,190,189]) else (if i.val < 231 then #[117,191,249,250] else #[127,249,191,251]))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then #[131,250,251,191] else #[119,193,192,252]) else (if i.val < 235 then #[125,194,252,192] else #[129,252,194,193])) else (if i.val < 238 then (if i.val < 237 then #[122,197,196,195] else #[120,199,198,253]) else (if i.val < 239 then #[126,200,253,198] else #[130,253,200,199])))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then #[123,203,202,201] else #[249,207,206,205]) else (if i.val < 243 then #[248,209,208,254] else #[252,210,254,208])) else (if i.val < 246 then (if i.val < 245 then #[253,254,210,209] else #[250,213,212,211]) else (if i.val < 247 then #[251,217,216,215] else #[254,222,221,220]))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then #[180,229,228,227] else #[179,231,230,255]) else (if i.val < 251 then #[183,232,255,230] else #[184,255,232,231])) else (if i.val < 254 then (if i.val < 253 then #[181,235,234,233] else #[182,239,238,237]) else (if i.val < 255 then #[255,244,243,242] else #[225,251,250,249]))))))))
private def betaWordTable (i : Fin 256) : List (Fin 4) :=
  (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then [] else [0]) else (if i.val < 3 then [1] else [2])) else (if i.val < 6 then (if i.val < 5 then [3] else [0,0]) else (if i.val < 7 then [0,1] else [0,2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then [0,3] else [1,0]) else (if i.val < 11 then [1,2] else [1,3])) else (if i.val < 14 then (if i.val < 13 then [2,0] else [2,3]) else (if i.val < 15 then [3,0] else [0,0,0])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then [0,0,1] else [0,0,2]) else (if i.val < 19 then [0,0,3] else [0,1,0])) else (if i.val < 22 then (if i.val < 21 then [0,1,2] else [0,1,3]) else (if i.val < 23 then [0,2,0] else [0,2,3]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then [0,3,0] else [1,0,1]) else (if i.val < 27 then [1,0,2] else [1,0,3])) else (if i.val < 30 then (if i.val < 29 then [1,2,0] else [1,2,3]) else (if i.val < 31 then [1,3,0] else [2,0,1]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then [2,0,2] else [2,0,3]) else (if i.val < 35 then [2,3,0] else [3,0,1])) else (if i.val < 38 then (if i.val < 37 then [3,0,2] else [3,0,3]) else (if i.val < 39 then [0,0,0,1] else [0,0,0,2]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then [0,0,0,3] else [0,0,1,0]) else (if i.val < 43 then [0,0,1,2] else [0,0,1,3])) else (if i.val < 46 then (if i.val < 45 then [0,0,2,0] else [0,0,2,3]) else (if i.val < 47 then [0,0,3,0] else [0,1,0,1])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then [0,1,0,2] else [0,1,0,3]) else (if i.val < 51 then [0,1,2,0] else [0,1,2,3])) else (if i.val < 54 then (if i.val < 53 then [0,1,3,0] else [0,2,0,1]) else (if i.val < 55 then [0,2,0,2] else [0,2,0,3]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then [0,2,3,0] else [0,3,0,1]) else (if i.val < 59 then [0,3,0,2] else [0,3,0,3])) else (if i.val < 62 then (if i.val < 61 then [1,0,1,2] else [1,0,1,3]) else (if i.val < 63 then [1,0,2,3] else [1,2,0,1])))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then [1,2,0,2] else [1,2,0,3]) else (if i.val < 67 then [1,2,3,0] else [1,3,0,1])) else (if i.val < 70 then (if i.val < 69 then [1,3,0,2] else [1,3,0,3]) else (if i.val < 71 then [2,0,1,2] else [2,0,1,3]))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then [2,0,2,3] else [2,3,0,1]) else (if i.val < 75 then [2,3,0,2] else [2,3,0,3])) else (if i.val < 78 then (if i.val < 77 then [3,0,1,2] else [3,0,1,3]) else (if i.val < 79 then [3,0,2,3] else [0,0,0,1,0])))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then [0,0,0,1,2] else [0,0,0,1,3]) else (if i.val < 83 then [0,0,0,2,0] else [0,0,0,2,3])) else (if i.val < 86 then (if i.val < 85 then [0,0,0,3,0] else [0,0,1,0,1]) else (if i.val < 87 then [0,0,1,0,2] else [0,0,1,0,3]))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then [0,0,1,2,0] else [0,0,1,2,3]) else (if i.val < 91 then [0,0,1,3,0] else [0,0,2,0,1])) else (if i.val < 94 then (if i.val < 93 then [0,0,2,0,2] else [0,0,2,0,3]) else (if i.val < 95 then [0,0,2,3,0] else [0,0,3,0,1]))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then [0,0,3,0,2] else [0,0,3,0,3]) else (if i.val < 99 then [0,1,0,1,2] else [0,1,0,1,3])) else (if i.val < 102 then (if i.val < 101 then [0,1,0,2,3] else [0,1,2,0,1]) else (if i.val < 103 then [0,1,2,0,2] else [0,1,2,0,3]))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then [0,1,2,3,0] else [0,1,3,0,1]) else (if i.val < 107 then [0,1,3,0,2] else [0,1,3,0,3])) else (if i.val < 110 then (if i.val < 109 then [0,2,0,1,2] else [0,2,0,1,3]) else (if i.val < 111 then [0,2,0,2,3] else [0,2,3,0,1])))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then [0,2,3,0,2] else [0,2,3,0,3]) else (if i.val < 115 then [0,3,0,1,2] else [0,3,0,1,3])) else (if i.val < 118 then (if i.val < 117 then [0,3,0,2,3] else [1,0,1,2,3]) else (if i.val < 119 then [1,2,0,1,2] else [1,2,0,1,3]))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then [1,2,0,2,3] else [1,2,3,0,1]) else (if i.val < 123 then [1,2,3,0,2] else [1,2,3,0,3])) else (if i.val < 126 then (if i.val < 125 then [1,3,0,1,2] else [1,3,0,1,3]) else (if i.val < 127 then [1,3,0,2,3] else [2,0,1,2,3]))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then [2,3,0,1,2] else [2,3,0,1,3]) else (if i.val < 131 then [2,3,0,2,3] else [3,0,1,2,3])) else (if i.val < 134 then (if i.val < 133 then [0,0,0,1,0,1] else [0,0,0,1,0,2]) else (if i.val < 135 then [0,0,0,1,0,3] else [0,0,0,1,2,0]))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then [0,0,0,1,2,3] else [0,0,0,1,3,0]) else (if i.val < 139 then [0,0,0,2,0,1] else [0,0,0,2,0,2])) else (if i.val < 142 then (if i.val < 141 then [0,0,0,2,0,3] else [0,0,0,2,3,0]) else (if i.val < 143 then [0,0,0,3,0,1] else [0,0,0,3,0,2])))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then [0,0,0,3,0,3] else [0,0,1,0,1,2]) else (if i.val < 147 then [0,0,1,0,1,3] else [0,0,1,0,2,3])) else (if i.val < 150 then (if i.val < 149 then [0,0,1,2,0,1] else [0,0,1,2,0,2]) else (if i.val < 151 then [0,0,1,2,0,3] else [0,0,1,2,3,0]))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then [0,0,1,3,0,1] else [0,0,1,3,0,2]) else (if i.val < 155 then [0,0,1,3,0,3] else [0,0,2,0,1,2])) else (if i.val < 158 then (if i.val < 157 then [0,0,2,0,1,3] else [0,0,2,0,2,3]) else (if i.val < 159 then [0,0,2,3,0,1] else [0,0,2,3,0,2]))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then [0,0,2,3,0,3] else [0,0,3,0,1,2]) else (if i.val < 163 then [0,0,3,0,1,3] else [0,0,3,0,2,3])) else (if i.val < 166 then (if i.val < 165 then [0,1,0,1,2,3] else [0,1,2,0,1,2]) else (if i.val < 167 then [0,1,2,0,1,3] else [0,1,2,0,2,3]))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then [0,1,2,3,0,1] else [0,1,2,3,0,2]) else (if i.val < 171 then [0,1,2,3,0,3] else [0,1,3,0,1,2])) else (if i.val < 174 then (if i.val < 173 then [0,1,3,0,1,3] else [0,1,3,0,2,3]) else (if i.val < 175 then [0,2,0,1,2,3] else [0,2,3,0,1,2])))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then [0,2,3,0,1,3] else [0,2,3,0,2,3]) else (if i.val < 179 then [0,3,0,1,2,3] else [1,2,0,1,2,3])) else (if i.val < 182 then (if i.val < 181 then [1,2,3,0,1,2] else [1,2,3,0,1,3]) else (if i.val < 183 then [1,2,3,0,2,3] else [1,3,0,1,2,3]))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then [2,3,0,1,2,3] else [0,0,0,1,0,1,2]) else (if i.val < 187 then [0,0,0,1,0,1,3] else [0,0,0,1,0,2,3])) else (if i.val < 190 then (if i.val < 189 then [0,0,0,1,2,0,1] else [0,0,0,1,2,0,2]) else (if i.val < 191 then [0,0,0,1,2,0,3] else [0,0,0,1,2,3,0])))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then [0,0,0,1,3,0,1] else [0,0,0,1,3,0,2]) else (if i.val < 195 then [0,0,0,1,3,0,3] else [0,0,0,2,0,1,2])) else (if i.val < 198 then (if i.val < 197 then [0,0,0,2,0,1,3] else [0,0,0,2,0,2,3]) else (if i.val < 199 then [0,0,0,2,3,0,1] else [0,0,0,2,3,0,2]))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then [0,0,0,2,3,0,3] else [0,0,0,3,0,1,2]) else (if i.val < 203 then [0,0,0,3,0,1,3] else [0,0,0,3,0,2,3])) else (if i.val < 206 then (if i.val < 205 then [0,0,1,0,1,2,3] else [0,0,1,2,0,1,2]) else (if i.val < 207 then [0,0,1,2,0,1,3] else [0,0,1,2,0,2,3])))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then [0,0,1,2,3,0,1] else [0,0,1,2,3,0,2]) else (if i.val < 211 then [0,0,1,2,3,0,3] else [0,0,1,3,0,1,2])) else (if i.val < 214 then (if i.val < 213 then [0,0,1,3,0,1,3] else [0,0,1,3,0,2,3]) else (if i.val < 215 then [0,0,2,0,1,2,3] else [0,0,2,3,0,1,2]))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then [0,0,2,3,0,1,3] else [0,0,2,3,0,2,3]) else (if i.val < 219 then [0,0,3,0,1,2,3] else [0,1,2,0,1,2,3])) else (if i.val < 222 then (if i.val < 221 then [0,1,2,3,0,1,2] else [0,1,2,3,0,1,3]) else (if i.val < 223 then [0,1,2,3,0,2,3] else [0,1,3,0,1,2,3]))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then [0,2,3,0,1,2,3] else [1,2,3,0,1,2,3]) else (if i.val < 227 then [0,0,0,1,0,1,2,3] else [0,0,0,1,2,0,1,2])) else (if i.val < 230 then (if i.val < 229 then [0,0,0,1,2,0,1,3] else [0,0,0,1,2,0,2,3]) else (if i.val < 231 then [0,0,0,1,2,3,0,1] else [0,0,0,1,2,3,0,2]))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then [0,0,0,1,2,3,0,3] else [0,0,0,1,3,0,1,2]) else (if i.val < 235 then [0,0,0,1,3,0,1,3] else [0,0,0,1,3,0,2,3])) else (if i.val < 238 then (if i.val < 237 then [0,0,0,2,0,1,2,3] else [0,0,0,2,3,0,1,2]) else (if i.val < 239 then [0,0,0,2,3,0,1,3] else [0,0,0,2,3,0,2,3])))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then [0,0,0,3,0,1,2,3] else [0,0,1,2,0,1,2,3]) else (if i.val < 243 then [0,0,1,2,3,0,1,2] else [0,0,1,2,3,0,1,3])) else (if i.val < 246 then (if i.val < 245 then [0,0,1,2,3,0,2,3] else [0,0,1,3,0,1,2,3]) else (if i.val < 247 then [0,0,2,3,0,1,2,3] else [0,1,2,3,0,1,2,3]))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then [0,0,0,1,2,0,1,2,3] else [0,0,0,1,2,3,0,1,2]) else (if i.val < 251 then [0,0,0,1,2,3,0,1,3] else [0,0,0,1,2,3,0,2,3])) else (if i.val < 254 then (if i.val < 253 then [0,0,0,1,3,0,1,2,3] else [0,0,0,2,3,0,1,2,3]) else (if i.val < 255 then [0,0,1,2,3,0,1,2,3] else [0,0,0,1,2,3,0,1,2,3]))))))))
private def betaCayley : FiniteCayleyCertificate (fun j => (betaGenerators j, betaImages j)) 256 where
  elements := (fun i => (betaSource i, betaTarget i))
  identity := 0
  identity_eq := by decide +kernel
  next i j := (betaNextTable i)[j.val]!
  next_eq := (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))))
  words i := betaWordTable i
  words_eq := (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))))

def betaCertificate : FiniteHomCertificate betaGenerators betaImages 256 where
  cayley := betaCayley
  first_kernel := (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))))

private def quotientElementLiteral0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral3 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral4 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral5 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral6 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral7 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral8 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral9 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral10 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral11 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral12 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral13 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral14 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral15 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral16 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral17 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral18 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral19 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral20 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral21 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral22 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral23 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral24 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral25 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral26 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral27 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral28 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral29 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral30 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral31 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral32 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral33 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral34 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral35 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral36 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral37 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral38 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral39 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral40 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral41 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral42 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral43 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral44 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral45 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral46 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral47 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral48 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral49 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral50 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral51 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral52 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral53 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral54 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral55 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral56 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral57 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral58 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral59 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral60 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral61 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral62 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral63 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral64 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral65 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral66 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral67 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral68 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral69 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral70 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral71 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral72 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral73 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral74 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral75 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral76 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral77 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral78 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral79 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral80 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral81 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral82 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral83 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral84 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral85 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral86 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral87 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral88 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral89 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral90 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral91 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral92 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral93 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral94 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral95 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral96 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral97 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral98 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral99 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral100 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral101 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral102 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral103 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral104 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral105 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral106 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral107 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral108 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral109 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral110 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral111 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral112 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral113 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral114 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral115 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral116 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral117 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral118 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral119 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral120 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral121 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral122 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral123 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral124 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral125 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral126 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral127 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral128 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral129 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral130 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral131 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral132 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral133 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral134 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral135 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral136 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral137 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral138 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral139 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral140 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral141 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral142 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral143 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral144 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral145 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral146 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral147 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral148 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral149 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral150 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral151 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral152 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral153 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral154 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral155 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral156 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral157 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral158 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral159 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral160 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral161 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral162 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral163 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral164 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral165 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral166 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral167 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral168 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral169 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral170 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral171 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral172 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral173 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral174 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral175 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral176 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral177 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral178 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral179 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral180 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral181 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral182 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral183 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral184 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral185 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral186 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral187 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral188 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral189 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral190 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral191 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral192 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral193 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral194 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral195 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral196 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral197 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral198 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral199 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral200 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral201 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral202 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral203 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral204 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral205 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral206 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral207 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral208 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral209 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral210 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral211 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral212 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral213 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral214 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral215 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral216 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral217 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral218 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral219 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral220 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral221 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral222 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral223 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral224 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral225 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral226 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral227 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral228 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral229 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral230 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral231 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral232 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral233 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral234 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral235 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral236 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral237 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral238 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral239 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral240 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral241 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral242 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral243 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral244 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral245 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral246 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral247 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral248 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral249 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral250 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral251 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral252 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral253 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral254 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElementLiteral255 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def quotientElement (i : Fin 256) : Equiv.Perm (Fin 16) :=
  (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then quotientElementLiteral0 else quotientElementLiteral1) else (if i.val < 3 then quotientElementLiteral2 else quotientElementLiteral3)) else (if i.val < 6 then (if i.val < 5 then quotientElementLiteral4 else quotientElementLiteral5) else (if i.val < 7 then quotientElementLiteral6 else quotientElementLiteral7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then quotientElementLiteral8 else quotientElementLiteral9) else (if i.val < 11 then quotientElementLiteral10 else quotientElementLiteral11)) else (if i.val < 14 then (if i.val < 13 then quotientElementLiteral12 else quotientElementLiteral13) else (if i.val < 15 then quotientElementLiteral14 else quotientElementLiteral15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then quotientElementLiteral16 else quotientElementLiteral17) else (if i.val < 19 then quotientElementLiteral18 else quotientElementLiteral19)) else (if i.val < 22 then (if i.val < 21 then quotientElementLiteral20 else quotientElementLiteral21) else (if i.val < 23 then quotientElementLiteral22 else quotientElementLiteral23))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then quotientElementLiteral24 else quotientElementLiteral25) else (if i.val < 27 then quotientElementLiteral26 else quotientElementLiteral27)) else (if i.val < 30 then (if i.val < 29 then quotientElementLiteral28 else quotientElementLiteral29) else (if i.val < 31 then quotientElementLiteral30 else quotientElementLiteral31))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then quotientElementLiteral32 else quotientElementLiteral33) else (if i.val < 35 then quotientElementLiteral34 else quotientElementLiteral35)) else (if i.val < 38 then (if i.val < 37 then quotientElementLiteral36 else quotientElementLiteral37) else (if i.val < 39 then quotientElementLiteral38 else quotientElementLiteral39))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then quotientElementLiteral40 else quotientElementLiteral41) else (if i.val < 43 then quotientElementLiteral42 else quotientElementLiteral43)) else (if i.val < 46 then (if i.val < 45 then quotientElementLiteral44 else quotientElementLiteral45) else (if i.val < 47 then quotientElementLiteral46 else quotientElementLiteral47)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then quotientElementLiteral48 else quotientElementLiteral49) else (if i.val < 51 then quotientElementLiteral50 else quotientElementLiteral51)) else (if i.val < 54 then (if i.val < 53 then quotientElementLiteral52 else quotientElementLiteral53) else (if i.val < 55 then quotientElementLiteral54 else quotientElementLiteral55))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then quotientElementLiteral56 else quotientElementLiteral57) else (if i.val < 59 then quotientElementLiteral58 else quotientElementLiteral59)) else (if i.val < 62 then (if i.val < 61 then quotientElementLiteral60 else quotientElementLiteral61) else (if i.val < 63 then quotientElementLiteral62 else quotientElementLiteral63)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then quotientElementLiteral64 else quotientElementLiteral65) else (if i.val < 67 then quotientElementLiteral66 else quotientElementLiteral67)) else (if i.val < 70 then (if i.val < 69 then quotientElementLiteral68 else quotientElementLiteral69) else (if i.val < 71 then quotientElementLiteral70 else quotientElementLiteral71))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then quotientElementLiteral72 else quotientElementLiteral73) else (if i.val < 75 then quotientElementLiteral74 else quotientElementLiteral75)) else (if i.val < 78 then (if i.val < 77 then quotientElementLiteral76 else quotientElementLiteral77) else (if i.val < 79 then quotientElementLiteral78 else quotientElementLiteral79)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then quotientElementLiteral80 else quotientElementLiteral81) else (if i.val < 83 then quotientElementLiteral82 else quotientElementLiteral83)) else (if i.val < 86 then (if i.val < 85 then quotientElementLiteral84 else quotientElementLiteral85) else (if i.val < 87 then quotientElementLiteral86 else quotientElementLiteral87))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then quotientElementLiteral88 else quotientElementLiteral89) else (if i.val < 91 then quotientElementLiteral90 else quotientElementLiteral91)) else (if i.val < 94 then (if i.val < 93 then quotientElementLiteral92 else quotientElementLiteral93) else (if i.val < 95 then quotientElementLiteral94 else quotientElementLiteral95))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then quotientElementLiteral96 else quotientElementLiteral97) else (if i.val < 99 then quotientElementLiteral98 else quotientElementLiteral99)) else (if i.val < 102 then (if i.val < 101 then quotientElementLiteral100 else quotientElementLiteral101) else (if i.val < 103 then quotientElementLiteral102 else quotientElementLiteral103))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then quotientElementLiteral104 else quotientElementLiteral105) else (if i.val < 107 then quotientElementLiteral106 else quotientElementLiteral107)) else (if i.val < 110 then (if i.val < 109 then quotientElementLiteral108 else quotientElementLiteral109) else (if i.val < 111 then quotientElementLiteral110 else quotientElementLiteral111)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then quotientElementLiteral112 else quotientElementLiteral113) else (if i.val < 115 then quotientElementLiteral114 else quotientElementLiteral115)) else (if i.val < 118 then (if i.val < 117 then quotientElementLiteral116 else quotientElementLiteral117) else (if i.val < 119 then quotientElementLiteral118 else quotientElementLiteral119))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then quotientElementLiteral120 else quotientElementLiteral121) else (if i.val < 123 then quotientElementLiteral122 else quotientElementLiteral123)) else (if i.val < 126 then (if i.val < 125 then quotientElementLiteral124 else quotientElementLiteral125) else (if i.val < 127 then quotientElementLiteral126 else quotientElementLiteral127))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then quotientElementLiteral128 else quotientElementLiteral129) else (if i.val < 131 then quotientElementLiteral130 else quotientElementLiteral131)) else (if i.val < 134 then (if i.val < 133 then quotientElementLiteral132 else quotientElementLiteral133) else (if i.val < 135 then quotientElementLiteral134 else quotientElementLiteral135))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then quotientElementLiteral136 else quotientElementLiteral137) else (if i.val < 139 then quotientElementLiteral138 else quotientElementLiteral139)) else (if i.val < 142 then (if i.val < 141 then quotientElementLiteral140 else quotientElementLiteral141) else (if i.val < 143 then quotientElementLiteral142 else quotientElementLiteral143)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then quotientElementLiteral144 else quotientElementLiteral145) else (if i.val < 147 then quotientElementLiteral146 else quotientElementLiteral147)) else (if i.val < 150 then (if i.val < 149 then quotientElementLiteral148 else quotientElementLiteral149) else (if i.val < 151 then quotientElementLiteral150 else quotientElementLiteral151))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then quotientElementLiteral152 else quotientElementLiteral153) else (if i.val < 155 then quotientElementLiteral154 else quotientElementLiteral155)) else (if i.val < 158 then (if i.val < 157 then quotientElementLiteral156 else quotientElementLiteral157) else (if i.val < 159 then quotientElementLiteral158 else quotientElementLiteral159))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then quotientElementLiteral160 else quotientElementLiteral161) else (if i.val < 163 then quotientElementLiteral162 else quotientElementLiteral163)) else (if i.val < 166 then (if i.val < 165 then quotientElementLiteral164 else quotientElementLiteral165) else (if i.val < 167 then quotientElementLiteral166 else quotientElementLiteral167))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then quotientElementLiteral168 else quotientElementLiteral169) else (if i.val < 171 then quotientElementLiteral170 else quotientElementLiteral171)) else (if i.val < 174 then (if i.val < 173 then quotientElementLiteral172 else quotientElementLiteral173) else (if i.val < 175 then quotientElementLiteral174 else quotientElementLiteral175)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then quotientElementLiteral176 else quotientElementLiteral177) else (if i.val < 179 then quotientElementLiteral178 else quotientElementLiteral179)) else (if i.val < 182 then (if i.val < 181 then quotientElementLiteral180 else quotientElementLiteral181) else (if i.val < 183 then quotientElementLiteral182 else quotientElementLiteral183))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then quotientElementLiteral184 else quotientElementLiteral185) else (if i.val < 187 then quotientElementLiteral186 else quotientElementLiteral187)) else (if i.val < 190 then (if i.val < 189 then quotientElementLiteral188 else quotientElementLiteral189) else (if i.val < 191 then quotientElementLiteral190 else quotientElementLiteral191)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then quotientElementLiteral192 else quotientElementLiteral193) else (if i.val < 195 then quotientElementLiteral194 else quotientElementLiteral195)) else (if i.val < 198 then (if i.val < 197 then quotientElementLiteral196 else quotientElementLiteral197) else (if i.val < 199 then quotientElementLiteral198 else quotientElementLiteral199))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then quotientElementLiteral200 else quotientElementLiteral201) else (if i.val < 203 then quotientElementLiteral202 else quotientElementLiteral203)) else (if i.val < 206 then (if i.val < 205 then quotientElementLiteral204 else quotientElementLiteral205) else (if i.val < 207 then quotientElementLiteral206 else quotientElementLiteral207)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then quotientElementLiteral208 else quotientElementLiteral209) else (if i.val < 211 then quotientElementLiteral210 else quotientElementLiteral211)) else (if i.val < 214 then (if i.val < 213 then quotientElementLiteral212 else quotientElementLiteral213) else (if i.val < 215 then quotientElementLiteral214 else quotientElementLiteral215))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then quotientElementLiteral216 else quotientElementLiteral217) else (if i.val < 219 then quotientElementLiteral218 else quotientElementLiteral219)) else (if i.val < 222 then (if i.val < 221 then quotientElementLiteral220 else quotientElementLiteral221) else (if i.val < 223 then quotientElementLiteral222 else quotientElementLiteral223))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then quotientElementLiteral224 else quotientElementLiteral225) else (if i.val < 227 then quotientElementLiteral226 else quotientElementLiteral227)) else (if i.val < 230 then (if i.val < 229 then quotientElementLiteral228 else quotientElementLiteral229) else (if i.val < 231 then quotientElementLiteral230 else quotientElementLiteral231))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then quotientElementLiteral232 else quotientElementLiteral233) else (if i.val < 235 then quotientElementLiteral234 else quotientElementLiteral235)) else (if i.val < 238 then (if i.val < 237 then quotientElementLiteral236 else quotientElementLiteral237) else (if i.val < 239 then quotientElementLiteral238 else quotientElementLiteral239)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then quotientElementLiteral240 else quotientElementLiteral241) else (if i.val < 243 then quotientElementLiteral242 else quotientElementLiteral243)) else (if i.val < 246 then (if i.val < 245 then quotientElementLiteral244 else quotientElementLiteral245) else (if i.val < 247 then quotientElementLiteral246 else quotientElementLiteral247))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then quotientElementLiteral248 else quotientElementLiteral249) else (if i.val < 251 then quotientElementLiteral250 else quotientElementLiteral251)) else (if i.val < 254 then (if i.val < 253 then quotientElementLiteral252 else quotientElementLiteral253) else (if i.val < 255 then quotientElementLiteral254 else quotientElementLiteral255))))))))

def quotientGenerators (j : Fin 4) := quotientElement (#[1,2,3,4][j.val]!)
private def quotientNextTable (i : Fin 256) : Array (Fin 256) :=
  (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[1,2,3,4] else #[5,6,7,8]) else (if i.val < 3 then #[9,0,10,11] else #[12,10,0,13])) else (if i.val < 6 then (if i.val < 5 then #[14,11,13,0] else #[15,16,17,18]) else (if i.val < 7 then #[19,1,20,21] else #[22,20,1,23]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[24,21,23,1] else #[16,25,26,27]) else (if i.val < 11 then #[28,3,2,29] else #[30,4,29,2])) else (if i.val < 14 then (if i.val < 13 then #[17,31,32,33] else #[34,29,4,3]) else (if i.val < 15 then #[18,35,36,37] else #[0,38,39,40])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then #[41,5,42,43] else #[44,42,5,45]) else (if i.val < 19 then #[46,43,45,5] else #[38,47,48,49])) else (if i.val < 22 then (if i.val < 21 then #[50,7,6,51] else #[52,8,51,6]) else (if i.val < 23 then #[39,53,54,55] else #[56,51,8,7]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then #[40,57,58,59] else #[47,9,60,61]) else (if i.val < 27 then #[53,60,9,62] else #[57,61,62,9])) else (if i.val < 30 then (if i.val < 29 then #[42,63,64,65] else #[66,13,11,10]) else (if i.val < 31 then #[43,67,68,69] else #[48,12,70,71]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then #[54,70,12,72] else #[58,71,72,12]) else (if i.val < 35 then #[45,73,74,75] else #[49,14,76,77])) else (if i.val < 38 then (if i.val < 37 then #[55,76,14,78] else #[59,77,78,14]) else (if i.val < 39 then #[79,15,80,81] else #[82,80,15,83]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then #[84,81,83,15] else #[2,85,86,87]) else (if i.val < 43 then #[88,17,16,89] else #[90,18,89,16])) else (if i.val < 46 then (if i.val < 45 then #[3,91,92,93] else #[94,89,18,17]) else (if i.val < 47 then #[4,95,96,97] else #[85,19,98,99])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then #[91,98,19,100] else #[95,99,100,19]) else (if i.val < 51 then #[80,101,102,103] else #[104,23,21,20])) else (if i.val < 54 then (if i.val < 53 then #[81,105,106,107] else #[86,22,108,109]) else (if i.val < 55 then #[92,108,22,110] else #[96,109,110,22]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then #[83,111,112,113] else #[87,24,114,115]) else (if i.val < 59 then #[93,114,24,116] else #[97,115,116,24])) else (if i.val < 62 then (if i.val < 61 then #[101,26,25,117] else #[105,27,117,25]) else (if i.val < 63 then #[111,117,27,26] else #[98,28,118,119])))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then #[108,118,28,120] else #[114,119,120,28]) else (if i.val < 67 then #[89,121,122,123] else #[99,30,124,125])) else (if i.val < 70 then (if i.val < 69 then #[109,124,30,126] else #[115,125,126,30]) else (if i.val < 71 then #[102,32,31,127] else #[106,33,127,31]))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then #[112,127,33,32] else #[100,34,128,129]) else (if i.val < 75 then #[110,128,34,130] else #[116,129,130,34])) else (if i.val < 78 then (if i.val < 77 then #[103,36,35,131] else #[107,37,131,35]) else (if i.val < 79 then #[113,131,37,36] else #[6,132,133,134])))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then #[135,39,38,136] else #[137,40,136,38]) else (if i.val < 83 then #[7,138,139,140] else #[141,136,40,39])) else (if i.val < 86 then (if i.val < 85 then #[8,142,143,144] else #[132,41,145,146]) else (if i.val < 87 then #[138,145,41,147] else #[142,146,147,41]))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then #[10,148,149,150] else #[151,45,43,42]) else (if i.val < 91 then #[11,152,153,154] else #[133,44,155,156])) else (if i.val < 94 then (if i.val < 93 then #[139,155,44,157] else #[143,156,157,44]) else (if i.val < 95 then #[13,158,159,160] else #[134,46,161,162]))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then #[140,161,46,163] else #[144,162,163,46]) else (if i.val < 99 then #[148,48,47,164] else #[152,49,164,47])) else (if i.val < 102 then (if i.val < 101 then #[158,164,49,48] else #[145,50,165,166]) else (if i.val < 103 then #[155,165,50,167] else #[161,166,167,50]))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then #[136,168,169,170] else #[146,52,171,172]) else (if i.val < 107 then #[156,171,52,173] else #[162,172,173,52])) else (if i.val < 110 then (if i.val < 109 then #[149,54,53,174] else #[153,55,174,53]) else (if i.val < 111 then #[159,174,55,54] else #[147,56,175,176])))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then #[157,175,56,177] else #[163,176,177,56]) else (if i.val < 115 then #[150,58,57,178] else #[154,59,178,57])) else (if i.val < 118 then (if i.val < 117 then #[160,178,59,58] else #[168,62,61,60]) else (if i.val < 119 then #[165,64,63,179] else #[171,65,179,63]))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then #[175,179,65,64] else #[164,66,180,181]) else (if i.val < 123 then #[174,180,66,182] else #[178,181,182,66])) else (if i.val < 126 then (if i.val < 125 then #[166,68,67,183] else #[172,69,183,67]) else (if i.val < 127 then #[176,183,69,68] else #[169,72,71,70]))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then #[167,74,73,184] else #[173,75,184,73]) else (if i.val < 131 then #[177,184,75,74] else #[170,78,77,76])) else (if i.val < 134 then (if i.val < 133 then #[25,79,185,186] else #[31,185,79,187]) else (if i.val < 135 then #[35,186,187,79] else #[20,188,189,190]))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then #[191,83,81,80] else #[21,192,193,194]) else (if i.val < 139 then #[26,82,195,196] else #[32,195,82,197])) else (if i.val < 142 then (if i.val < 141 then #[36,196,197,82] else #[23,198,199,200]) else (if i.val < 143 then #[27,84,201,202] else #[33,201,84,203])))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then #[37,202,203,84] else #[188,86,85,204]) else (if i.val < 147 then #[192,87,204,85] else #[198,204,87,86])) else (if i.val < 150 then (if i.val < 149 then #[185,88,205,206] else #[195,205,88,207]) else (if i.val < 151 then #[201,206,207,88] else #[29,208,209,210]))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then #[186,90,211,212] else #[196,211,90,213]) else (if i.val < 155 then #[202,212,213,90] else #[189,92,91,214])) else (if i.val < 158 then (if i.val < 157 then #[193,93,214,91] else #[199,214,93,92]) else (if i.val < 159 then #[187,94,215,216] else #[197,215,94,217]))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then #[203,216,217,94] else #[190,96,95,218]) else (if i.val < 163 then #[194,97,218,95] else #[200,218,97,96])) else (if i.val < 166 then (if i.val < 165 then #[208,100,99,98] else #[205,102,101,219]) else (if i.val < 167 then #[211,103,219,101] else #[215,219,103,102]))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then #[204,104,220,221] else #[214,220,104,222]) else (if i.val < 171 then #[218,221,222,104] else #[206,106,105,223])) else (if i.val < 174 then (if i.val < 173 then #[212,107,223,105] else #[216,223,107,106]) else (if i.val < 175 then #[209,110,109,108] else #[207,112,111,224])))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then #[213,113,224,111] else #[217,224,113,112]) else (if i.val < 179 then #[210,116,115,114] else #[220,120,119,118])) else (if i.val < 182 then (if i.val < 181 then #[219,122,121,225] else #[223,123,225,121]) else (if i.val < 183 then #[224,225,123,122] else #[221,126,125,124]))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then #[222,130,129,128] else #[63,133,132,226]) else (if i.val < 187 then #[67,134,226,132] else #[73,226,134,133])) else (if i.val < 190 then (if i.val < 189 then #[60,135,227,228] else #[70,227,135,229]) else (if i.val < 191 then #[76,228,229,135] else #[51,230,231,232])))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then #[61,137,233,234] else #[71,233,137,235]) else (if i.val < 195 then #[77,234,235,137] else #[64,139,138,236])) else (if i.val < 198 then (if i.val < 197 then #[68,140,236,138] else #[74,236,140,139]) else (if i.val < 199 then #[62,141,237,238] else #[72,237,141,239]))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then #[78,238,239,141] else #[65,143,142,240]) else (if i.val < 203 then #[69,144,240,142] else #[75,240,144,143])) else (if i.val < 206 then (if i.val < 205 then #[230,147,146,145] else #[227,149,148,241]) else (if i.val < 207 then #[233,150,241,148] else #[237,241,150,149])))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then #[226,151,242,243] else #[236,242,151,244]) else (if i.val < 211 then #[240,243,244,151] else #[228,153,152,245])) else (if i.val < 214 then (if i.val < 213 then #[234,154,245,152] else #[238,245,154,153]) else (if i.val < 215 then #[231,157,156,155] else #[229,159,158,246]))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then #[235,160,246,158] else #[239,246,160,159]) else (if i.val < 219 then #[232,163,162,161] else #[242,167,166,165])) else (if i.val < 222 then (if i.val < 221 then #[241,169,168,247] else #[245,170,247,168]) else (if i.val < 223 then #[246,247,170,169] else #[243,173,172,171]))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then #[244,177,176,175] else #[247,182,181,180]) else (if i.val < 227 then #[121,187,186,185] else #[118,189,188,248])) else (if i.val < 230 then (if i.val < 229 then #[124,190,248,188] else #[128,248,190,189]) else (if i.val < 231 then #[117,191,249,250] else #[127,249,191,251]))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then #[131,250,251,191] else #[119,193,192,252]) else (if i.val < 235 then #[125,194,252,192] else #[129,252,194,193])) else (if i.val < 238 then (if i.val < 237 then #[122,197,196,195] else #[120,199,198,253]) else (if i.val < 239 then #[126,200,253,198] else #[130,253,200,199])))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then #[123,203,202,201] else #[249,207,206,205]) else (if i.val < 243 then #[248,209,208,254] else #[252,210,254,208])) else (if i.val < 246 then (if i.val < 245 then #[253,254,210,209] else #[250,213,212,211]) else (if i.val < 247 then #[251,217,216,215] else #[254,222,221,220]))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then #[180,229,228,227] else #[179,231,230,255]) else (if i.val < 251 then #[183,232,255,230] else #[184,255,232,231])) else (if i.val < 254 then (if i.val < 253 then #[181,235,234,233] else #[182,239,238,237]) else (if i.val < 255 then #[255,244,243,242] else #[225,251,250,249]))))))))
private def quotientWordTable (i : Fin 256) : List (Fin 4) :=
  (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then [] else [0]) else (if i.val < 3 then [1] else [2])) else (if i.val < 6 then (if i.val < 5 then [3] else [0,0]) else (if i.val < 7 then [0,1] else [0,2]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then [0,3] else [1,0]) else (if i.val < 11 then [1,2] else [1,3])) else (if i.val < 14 then (if i.val < 13 then [2,0] else [2,3]) else (if i.val < 15 then [3,0] else [0,0,0])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then [0,0,1] else [0,0,2]) else (if i.val < 19 then [0,0,3] else [0,1,0])) else (if i.val < 22 then (if i.val < 21 then [0,1,2] else [0,1,3]) else (if i.val < 23 then [0,2,0] else [0,2,3]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then [0,3,0] else [1,0,1]) else (if i.val < 27 then [1,0,2] else [1,0,3])) else (if i.val < 30 then (if i.val < 29 then [1,2,0] else [1,2,3]) else (if i.val < 31 then [1,3,0] else [2,0,1]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then [2,0,2] else [2,0,3]) else (if i.val < 35 then [2,3,0] else [3,0,1])) else (if i.val < 38 then (if i.val < 37 then [3,0,2] else [3,0,3]) else (if i.val < 39 then [0,0,0,1] else [0,0,0,2]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then [0,0,0,3] else [0,0,1,0]) else (if i.val < 43 then [0,0,1,2] else [0,0,1,3])) else (if i.val < 46 then (if i.val < 45 then [0,0,2,0] else [0,0,2,3]) else (if i.val < 47 then [0,0,3,0] else [0,1,0,1])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then [0,1,0,2] else [0,1,0,3]) else (if i.val < 51 then [0,1,2,0] else [0,1,2,3])) else (if i.val < 54 then (if i.val < 53 then [0,1,3,0] else [0,2,0,1]) else (if i.val < 55 then [0,2,0,2] else [0,2,0,3]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then [0,2,3,0] else [0,3,0,1]) else (if i.val < 59 then [0,3,0,2] else [0,3,0,3])) else (if i.val < 62 then (if i.val < 61 then [1,0,1,2] else [1,0,1,3]) else (if i.val < 63 then [1,0,2,3] else [1,2,0,1])))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then [1,2,0,2] else [1,2,0,3]) else (if i.val < 67 then [1,2,3,0] else [1,3,0,1])) else (if i.val < 70 then (if i.val < 69 then [1,3,0,2] else [1,3,0,3]) else (if i.val < 71 then [2,0,1,2] else [2,0,1,3]))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then [2,0,2,3] else [2,3,0,1]) else (if i.val < 75 then [2,3,0,2] else [2,3,0,3])) else (if i.val < 78 then (if i.val < 77 then [3,0,1,2] else [3,0,1,3]) else (if i.val < 79 then [3,0,2,3] else [0,0,0,1,0])))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then [0,0,0,1,2] else [0,0,0,1,3]) else (if i.val < 83 then [0,0,0,2,0] else [0,0,0,2,3])) else (if i.val < 86 then (if i.val < 85 then [0,0,0,3,0] else [0,0,1,0,1]) else (if i.val < 87 then [0,0,1,0,2] else [0,0,1,0,3]))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then [0,0,1,2,0] else [0,0,1,2,3]) else (if i.val < 91 then [0,0,1,3,0] else [0,0,2,0,1])) else (if i.val < 94 then (if i.val < 93 then [0,0,2,0,2] else [0,0,2,0,3]) else (if i.val < 95 then [0,0,2,3,0] else [0,0,3,0,1]))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then [0,0,3,0,2] else [0,0,3,0,3]) else (if i.val < 99 then [0,1,0,1,2] else [0,1,0,1,3])) else (if i.val < 102 then (if i.val < 101 then [0,1,0,2,3] else [0,1,2,0,1]) else (if i.val < 103 then [0,1,2,0,2] else [0,1,2,0,3]))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then [0,1,2,3,0] else [0,1,3,0,1]) else (if i.val < 107 then [0,1,3,0,2] else [0,1,3,0,3])) else (if i.val < 110 then (if i.val < 109 then [0,2,0,1,2] else [0,2,0,1,3]) else (if i.val < 111 then [0,2,0,2,3] else [0,2,3,0,1])))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then [0,2,3,0,2] else [0,2,3,0,3]) else (if i.val < 115 then [0,3,0,1,2] else [0,3,0,1,3])) else (if i.val < 118 then (if i.val < 117 then [0,3,0,2,3] else [1,0,1,2,3]) else (if i.val < 119 then [1,2,0,1,2] else [1,2,0,1,3]))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then [1,2,0,2,3] else [1,2,3,0,1]) else (if i.val < 123 then [1,2,3,0,2] else [1,2,3,0,3])) else (if i.val < 126 then (if i.val < 125 then [1,3,0,1,2] else [1,3,0,1,3]) else (if i.val < 127 then [1,3,0,2,3] else [2,0,1,2,3]))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then [2,3,0,1,2] else [2,3,0,1,3]) else (if i.val < 131 then [2,3,0,2,3] else [3,0,1,2,3])) else (if i.val < 134 then (if i.val < 133 then [0,0,0,1,0,1] else [0,0,0,1,0,2]) else (if i.val < 135 then [0,0,0,1,0,3] else [0,0,0,1,2,0]))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then [0,0,0,1,2,3] else [0,0,0,1,3,0]) else (if i.val < 139 then [0,0,0,2,0,1] else [0,0,0,2,0,2])) else (if i.val < 142 then (if i.val < 141 then [0,0,0,2,0,3] else [0,0,0,2,3,0]) else (if i.val < 143 then [0,0,0,3,0,1] else [0,0,0,3,0,2])))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then [0,0,0,3,0,3] else [0,0,1,0,1,2]) else (if i.val < 147 then [0,0,1,0,1,3] else [0,0,1,0,2,3])) else (if i.val < 150 then (if i.val < 149 then [0,0,1,2,0,1] else [0,0,1,2,0,2]) else (if i.val < 151 then [0,0,1,2,0,3] else [0,0,1,2,3,0]))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then [0,0,1,3,0,1] else [0,0,1,3,0,2]) else (if i.val < 155 then [0,0,1,3,0,3] else [0,0,2,0,1,2])) else (if i.val < 158 then (if i.val < 157 then [0,0,2,0,1,3] else [0,0,2,0,2,3]) else (if i.val < 159 then [0,0,2,3,0,1] else [0,0,2,3,0,2]))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then [0,0,2,3,0,3] else [0,0,3,0,1,2]) else (if i.val < 163 then [0,0,3,0,1,3] else [0,0,3,0,2,3])) else (if i.val < 166 then (if i.val < 165 then [0,1,0,1,2,3] else [0,1,2,0,1,2]) else (if i.val < 167 then [0,1,2,0,1,3] else [0,1,2,0,2,3]))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then [0,1,2,3,0,1] else [0,1,2,3,0,2]) else (if i.val < 171 then [0,1,2,3,0,3] else [0,1,3,0,1,2])) else (if i.val < 174 then (if i.val < 173 then [0,1,3,0,1,3] else [0,1,3,0,2,3]) else (if i.val < 175 then [0,2,0,1,2,3] else [0,2,3,0,1,2])))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then [0,2,3,0,1,3] else [0,2,3,0,2,3]) else (if i.val < 179 then [0,3,0,1,2,3] else [1,2,0,1,2,3])) else (if i.val < 182 then (if i.val < 181 then [1,2,3,0,1,2] else [1,2,3,0,1,3]) else (if i.val < 183 then [1,2,3,0,2,3] else [1,3,0,1,2,3]))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then [2,3,0,1,2,3] else [0,0,0,1,0,1,2]) else (if i.val < 187 then [0,0,0,1,0,1,3] else [0,0,0,1,0,2,3])) else (if i.val < 190 then (if i.val < 189 then [0,0,0,1,2,0,1] else [0,0,0,1,2,0,2]) else (if i.val < 191 then [0,0,0,1,2,0,3] else [0,0,0,1,2,3,0])))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then [0,0,0,1,3,0,1] else [0,0,0,1,3,0,2]) else (if i.val < 195 then [0,0,0,1,3,0,3] else [0,0,0,2,0,1,2])) else (if i.val < 198 then (if i.val < 197 then [0,0,0,2,0,1,3] else [0,0,0,2,0,2,3]) else (if i.val < 199 then [0,0,0,2,3,0,1] else [0,0,0,2,3,0,2]))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then [0,0,0,2,3,0,3] else [0,0,0,3,0,1,2]) else (if i.val < 203 then [0,0,0,3,0,1,3] else [0,0,0,3,0,2,3])) else (if i.val < 206 then (if i.val < 205 then [0,0,1,0,1,2,3] else [0,0,1,2,0,1,2]) else (if i.val < 207 then [0,0,1,2,0,1,3] else [0,0,1,2,0,2,3])))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then [0,0,1,2,3,0,1] else [0,0,1,2,3,0,2]) else (if i.val < 211 then [0,0,1,2,3,0,3] else [0,0,1,3,0,1,2])) else (if i.val < 214 then (if i.val < 213 then [0,0,1,3,0,1,3] else [0,0,1,3,0,2,3]) else (if i.val < 215 then [0,0,2,0,1,2,3] else [0,0,2,3,0,1,2]))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then [0,0,2,3,0,1,3] else [0,0,2,3,0,2,3]) else (if i.val < 219 then [0,0,3,0,1,2,3] else [0,1,2,0,1,2,3])) else (if i.val < 222 then (if i.val < 221 then [0,1,2,3,0,1,2] else [0,1,2,3,0,1,3]) else (if i.val < 223 then [0,1,2,3,0,2,3] else [0,1,3,0,1,2,3]))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then [0,2,3,0,1,2,3] else [1,2,3,0,1,2,3]) else (if i.val < 227 then [0,0,0,1,0,1,2,3] else [0,0,0,1,2,0,1,2])) else (if i.val < 230 then (if i.val < 229 then [0,0,0,1,2,0,1,3] else [0,0,0,1,2,0,2,3]) else (if i.val < 231 then [0,0,0,1,2,3,0,1] else [0,0,0,1,2,3,0,2]))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then [0,0,0,1,2,3,0,3] else [0,0,0,1,3,0,1,2]) else (if i.val < 235 then [0,0,0,1,3,0,1,3] else [0,0,0,1,3,0,2,3])) else (if i.val < 238 then (if i.val < 237 then [0,0,0,2,0,1,2,3] else [0,0,0,2,3,0,1,2]) else (if i.val < 239 then [0,0,0,2,3,0,1,3] else [0,0,0,2,3,0,2,3])))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then [0,0,0,3,0,1,2,3] else [0,0,1,2,0,1,2,3]) else (if i.val < 243 then [0,0,1,2,3,0,1,2] else [0,0,1,2,3,0,1,3])) else (if i.val < 246 then (if i.val < 245 then [0,0,1,2,3,0,2,3] else [0,0,1,3,0,1,2,3]) else (if i.val < 247 then [0,0,2,3,0,1,2,3] else [0,1,2,3,0,1,2,3]))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then [0,0,0,1,2,0,1,2,3] else [0,0,0,1,2,3,0,1,2]) else (if i.val < 251 then [0,0,0,1,2,3,0,1,3] else [0,0,0,1,2,3,0,2,3])) else (if i.val < 254 then (if i.val < 253 then [0,0,0,1,3,0,1,2,3] else [0,0,0,2,3,0,1,2,3]) else (if i.val < 255 then [0,0,1,2,3,0,1,2,3] else [0,0,0,1,2,3,0,1,2,3]))))))))
private def quotientCayley : FiniteCayleyCertificate quotientGenerators 256 where
  elements := quotientElement
  identity := 0
  identity_eq := by decide +kernel
  next i j := (quotientNextTable i)[j.val]!
  next_eq := (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))))
  words i := quotientWordTable i
  words_eq := (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))))

def quotientCertificate := quotientCayley

private def axisElementLiteral0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def axisElementLiteral1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def axisElementLiteral2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def axisElementLiteral3 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def axisElement (i : Fin 4) : Equiv.Perm (Fin 16) :=
  (if i.val < 2 then (if i.val < 1 then axisElementLiteral0 else axisElementLiteral1) else (if i.val < 3 then axisElementLiteral2 else axisElementLiteral3))

def axisGenerators (j : Fin 2) := axisElement (#[1,2][j.val]!)
private def axisNextTable (i : Fin 4) : Array (Fin 4) :=
  (if i.val < 2 then (if i.val < 1 then #[1,2] else #[0,3]) else (if i.val < 3 then #[3,0] else #[2,1]))
private def axisWordTable (i : Fin 4) : List (Fin 2) :=
  (if i.val < 2 then (if i.val < 1 then [] else [0]) else (if i.val < 3 then [1] else [0,1]))
private def axisCayley : FiniteCayleyCertificate axisGenerators 4 where
  elements := axisElement
  identity := 0
  identity_eq := by decide +kernel
  next i j := (axisNextTable i)[j.val]!
  next_eq := (by decide +kernel)
  words i := axisWordTable i
  words_eq := (by decide +kernel)

def axisCertificate := axisCayley

private def coverKernelElementLiteral0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def coverKernelElement (i : Fin 1) : Equiv.Perm (Fin 16) :=
  coverKernelElementLiteral0

def coverKernelGenerators (j : Fin 0) := coverKernelElement (#[][j.val]!)
private def coverKernelNextTable (i : Fin 1) : Array (Fin 1) :=
  #[]
private def coverKernelWordTable (i : Fin 1) : List (Fin 0) :=
  []
private def coverKernelCayley : FiniteCayleyCertificate coverKernelGenerators 1 where
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
    (fun i => (if i.val < 512 then (if i.val < 256 then (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 3) else (if i.val < 3 then 4 else 2)) else (if i.val < 6 then (if i.val < 5 then 1 else 13) else (if i.val < 7 then 10 else 12))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 11 else 14) else (if i.val < 11 then 10 else 11)) else (if i.val < 14 then (if i.val < 13 then 0 else 9) else (if i.val < 15 then 7 else 8)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 6 else 5) else (if i.val < 19 then 29 else 34)) else (if i.val < 22 then (if i.val < 21 then 2 else 29) else (if i.val < 23 then 3 else 28))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 32 else 33) else (if i.val < 27 then 31 else 17)) else (if i.val < 30 then (if i.val < 29 then 29 else 2) else (if i.val < 31 then 4 else 30))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 36 else 37) else (if i.val < 35 then 35 else 18)) else (if i.val < 38 then (if i.val < 37 then 29 else 3) else (if i.val < 39 then 28 else 4))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 30 else 2) else (if i.val < 43 then 1 else 26)) else (if i.val < 46 then (if i.val < 45 then 27 else 25) else (if i.val < 47 then 16 else 23)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 20 else 22) else (if i.val < 51 then 21 else 24)) else (if i.val < 54 then (if i.val < 53 then 20 else 21) else (if i.val < 55 then 19 else 17))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 18 else 15) else (if i.val < 59 then 11 else 10)) else (if i.val < 62 then (if i.val < 61 then 13 else 66) else (if i.val < 63 then 74 else 75)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 73 else 45) else (if i.val < 67 then 11 else 0)) else (if i.val < 70 then (if i.val < 69 then 9 else 13) else (if i.val < 71 then 66 else 10))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 12 else 64) else (if i.val < 75 then 65 else 63)) else (if i.val < 78 then (if i.val < 77 then 42 else 72) else (if i.val < 79 then 70 else 54)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 71 else 58) else (if i.val < 83 then 70 else 71)) else (if i.val < 86 then (if i.val < 85 then 48 else 5) else (if i.val < 87 then 45 else 44))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 13 else 66) else (if i.val < 91 then 0 else 9)) else (if i.val < 94 then (if i.val < 93 then 14 else 68) else (if i.val < 95 then 69 else 67))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 43 else 78) else (if i.val < 99 then 76 else 55)) else (if i.val < 102 then (if i.val < 101 then 77 else 59) else (if i.val < 103 then 76 else 77))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 49 else 45) else (if i.val < 107 then 5 else 46)) else (if i.val < 110 then (if i.val < 109 then 66 else 12) else (if i.val < 111 then 64 else 65)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 63 else 42) else (if i.val < 115 then 14 else 68)) else (if i.val < 118 then (if i.val < 117 then 69 else 67) else (if i.val < 119 then 43 else 9))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 7 else 8) else (if i.val < 123 then 6 else 5)) else (if i.val < 126 then (if i.val < 125 then 62 else 60) else (if i.val < 127 then 53 else 61))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 57 else 60) else (if i.val < 131 then 61 else 47)) else (if i.val < 134 then (if i.val < 133 then 41 else 51) else (if i.val < 135 then 56 else 6))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 51 else 50) else (if i.val < 139 then 54 else 55)) else (if i.val < 142 then (if i.val < 141 then 53 else 39) else (if i.val < 143 then 51 else 6)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 52 else 58) else (if i.val < 147 then 59 else 40)) else (if i.val < 150 then (if i.val < 149 then 51 else 7) else (if i.val < 151 then 50 else 8))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 52 else 49) else (if i.val < 155 then 47 else 38)) else (if i.val < 158 then (if i.val < 157 then 45 else 44) else (if i.val < 159 then 46 else 39))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 40 else 4) else (if i.val < 163 then 30 else 3)) else (if i.val < 166 then (if i.val < 165 then 28 else 34) else (if i.val < 167 then 122 else 123))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 121 else 89) else (if i.val < 171 then 130 else 128)) else (if i.val < 174 then (if i.val < 173 then 110 else 129) else (if i.val < 175 then 116 else 128)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 129 else 100) else (if i.val < 179 then 18 else 17)) else (if i.val < 182 then (if i.val < 181 then 94 else 30) else (if i.val < 183 then 1 else 26))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 27 else 25) else (if i.val < 187 then 16 else 34)) else (if i.val < 190 then (if i.val < 189 then 122 else 123) else (if i.val < 191 then 121 else 89)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 28 else 32) else (if i.val < 195 then 33 else 31)) else (if i.val < 198 then (if i.val < 197 then 17 else 120) else (if i.val < 199 then 118 else 108))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 119 else 114) else (if i.val < 203 then 118 else 119)) else (if i.val < 206 then (if i.val < 205 then 98 else 88) else (if i.val < 207 then 127 else 112)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 31 else 127) else (if i.val < 211 then 102 else 22)) else (if i.val < 214 then (if i.val < 213 then 110 else 108) else (if i.val < 215 then 92 else 127))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 31 else 106) else (if i.val < 219 then 24 else 116)) else (if i.val < 222 then (if i.val < 221 then 93 else 127) else (if i.val < 223 then 32 else 102))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 33 else 106) else (if i.val < 227 then 100 else 98)) else (if i.val < 230 then (if i.val < 229 then 91 else 18) else (if i.val < 231 then 15 else 94))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 92 else 93) else (if i.val < 235 then 34 else 122)) else (if i.val < 238 then (if i.val < 237 then 123 else 121) else (if i.val < 239 then 89 else 1)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 26 else 27) else (if i.val < 243 then 25 else 16)) else (if i.val < 246 then (if i.val < 245 then 36 else 37) else (if i.val < 247 then 35 else 126))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 124 else 109) else (if i.val < 251 then 125 else 115)) else (if i.val < 254 then (if i.val < 253 then 124 else 125) else (if i.val < 255 then 99 else 90)))))))) else (if i.val < 384 then (if i.val < 320 then (if i.val < 288 then (if i.val < 272 then (if i.val < 264 then (if i.val < 260 then (if i.val < 258 then (if i.val < 257 then 131 else 113) else (if i.val < 259 then 35 else 131)) else (if i.val < 262 then (if i.val < 261 then 103 else 110) else (if i.val < 263 then 22 else 109))) else (if i.val < 268 then (if i.val < 266 then (if i.val < 265 then 96 else 131) else (if i.val < 267 then 35 else 107)) else (if i.val < 270 then (if i.val < 269 then 116 else 24) else (if i.val < 271 then 97 else 131)))) else (if i.val < 280 then (if i.val < 276 then (if i.val < 274 then (if i.val < 273 then 36 else 103) else (if i.val < 275 then 37 else 107)) else (if i.val < 278 then (if i.val < 277 then 19 else 99) else (if i.val < 279 then 95 else 94))) else (if i.val < 284 then (if i.val < 282 then (if i.val < 281 then 15 else 96) else (if i.val < 283 then 97 else 122)) else (if i.val < 286 then (if i.val < 285 then 123 else 121) else (if i.val < 287 then 89 else 32))))) else (if i.val < 304 then (if i.val < 296 then (if i.val < 292 then (if i.val < 290 then (if i.val < 289 then 120 else 118) else (if i.val < 291 then 108 else 114)) else (if i.val < 294 then (if i.val < 293 then 118 else 98) else (if i.val < 295 then 88 else 37))) else (if i.val < 300 then (if i.val < 298 then (if i.val < 297 then 126 else 125) else (if i.val < 299 then 115 else 125)) else (if i.val < 302 then (if i.val < 301 then 99 else 90) else (if i.val < 303 then 26 else 27)))) else (if i.val < 312 then (if i.val < 308 then (if i.val < 306 then (if i.val < 305 then 25 else 16) else (if i.val < 307 then 23 else 20)) else (if i.val < 310 then (if i.val < 309 then 22 else 21) else (if i.val < 311 then 24 else 20))) else (if i.val < 316 then (if i.val < 314 then (if i.val < 313 then 21 else 19) else (if i.val < 315 then 15 else 117)) else (if i.val < 318 then (if i.val < 317 then 111 else 117) else (if i.val < 319 then 101 else 86)))))) else (if i.val < 352 then (if i.val < 336 then (if i.val < 328 then (if i.val < 324 then (if i.val < 322 then (if i.val < 321 then 117 else 105) else (if i.val < 323 then 87 else 117)) else (if i.val < 326 then (if i.val < 325 then 101 else 105) else (if i.val < 327 then 85 else 86))) else (if i.val < 332 then (if i.val < 330 then (if i.val < 329 then 87 else 104) else (if i.val < 331 then 112 else 113)) else (if i.val < 334 then (if i.val < 333 then 111 else 83) else (if i.val < 335 then 23 else 104)))) else (if i.val < 344 then (if i.val < 340 then (if i.val < 338 then (if i.val < 337 then 101 else 80) else (if i.val < 339 then 110 else 108)) else (if i.val < 342 then (if i.val < 341 then 92 else 83) else (if i.val < 343 then 82 else 23))) else (if i.val < 348 then (if i.val < 346 then (if i.val < 345 then 104 else 19) else (if i.val < 347 then 107 else 105)) else (if i.val < 350 then (if i.val < 349 then 81 else 116) else (if i.val < 351 then 97 else 83))))) else (if i.val < 368 then (if i.val < 360 then (if i.val < 356 then (if i.val < 354 then (if i.val < 353 then 84 else 104) else (if i.val < 355 then 101 else 80)) else (if i.val < 358 then (if i.val < 357 then 107 else 105) else (if i.val < 359 then 81 else 99))) else (if i.val < 364 then (if i.val < 362 then (if i.val < 361 then 95 else 98) else (if i.val < 363 then 85 else 79)) else (if i.val < 366 then (if i.val < 365 then 94 else 92) else (if i.val < 367 then 91 else 97)))) else (if i.val < 376 then (if i.val < 372 then (if i.val < 370 then (if i.val < 369 then 83 else 82) else (if i.val < 371 then 84 else 14)) else (if i.val < 374 then (if i.val < 373 then 68 else 69) else (if i.val < 375 then 67 else 43))) else (if i.val < 380 then (if i.val < 378 then (if i.val < 377 then 12 else 64) else (if i.val < 379 then 65 else 63)) else (if i.val < 382 then (if i.val < 381 then 42 else 74) else (if i.val < 383 then 75 else 73))))))) else (if i.val < 448 then (if i.val < 416 then (if i.val < 400 then (if i.val < 392 then (if i.val < 388 then (if i.val < 386 then (if i.val < 385 then 182 else 180) else (if i.val < 387 then 174 else 181)) else (if i.val < 390 then (if i.val < 389 then 178 else 180) else (if i.val < 391 then 181 else 164))) else (if i.val < 396 then (if i.val < 394 then (if i.val < 393 then 151 else 184) else (if i.val < 395 then 177 else 73)) else (if i.val < 398 then (if i.val < 397 then 184 else 167) else (if i.val < 399 then 55 else 54)))) else (if i.val < 408 then (if i.val < 404 then (if i.val < 402 then (if i.val < 401 then 174 else 159) else (if i.val < 403 then 184 else 73)) else (if i.val < 406 then (if i.val < 405 then 173 else 59) else (if i.val < 407 then 58 else 160))) else (if i.val < 412 then (if i.val < 410 then (if i.val < 409 then 184 else 74) else (if i.val < 411 then 167 else 75)) else (if i.val < 414 then (if i.val < 413 then 173 else 48) else (if i.val < 415 then 164 else 158))))) else (if i.val < 432 then (if i.val < 424 then (if i.val < 420 then (if i.val < 418 then (if i.val < 417 then 46 else 44) else (if i.val < 419 then 159 else 160)) else (if i.val < 422 then (if i.val < 421 then 68 else 69) else (if i.val < 423 then 67 else 43))) else (if i.val < 428 then (if i.val < 426 then (if i.val < 425 then 7 else 62) else (if i.val < 427 then 60 else 53)) else (if i.val < 430 then (if i.val < 429 then 57 else 60) else (if i.val < 431 then 47 else 41)))) else (if i.val < 440 then (if i.val < 436 then (if i.val < 434 then (if i.val < 433 then 75 else 182) else (if i.val < 435 then 181 else 178)) else (if i.val < 438 then (if i.val < 437 then 181 else 164) else (if i.val < 439 then 151 else 64))) else (if i.val < 444 then (if i.val < 442 then (if i.val < 441 then 65 else 63) else (if i.val < 443 then 42 else 72)) else (if i.val < 446 then (if i.val < 445 then 70 else 54) else (if i.val < 447 then 71 else 58)))))) else (if i.val < 480 then (if i.val < 464 then (if i.val < 456 then (if i.val < 452 then (if i.val < 450 then (if i.val < 449 then 70 else 71) else (if i.val < 451 then 48 else 44)) else (if i.val < 454 then (if i.val < 453 then 179 else 175) else (if i.val < 455 then 179 else 165))) else (if i.val < 460 then (if i.val < 458 then (if i.val < 457 then 149 else 179) else (if i.val < 459 then 171 else 150)) else (if i.val < 462 then (if i.val < 461 then 179 else 165) else (if i.val < 463 then 171 else 148)))) else (if i.val < 472 then (if i.val < 468 then (if i.val < 466 then (if i.val < 465 then 149 else 150) else (if i.val < 467 then 169 else 56)) else (if i.val < 470 then (if i.val < 469 then 177 else 175) else (if i.val < 471 then 157 else 72))) else (if i.val < 476 then (if i.val < 474 then (if i.val < 473 then 169 else 165) else (if i.val < 475 then 155 else 55)) else (if i.val < 478 then (if i.val < 477 then 53 else 39) else (if i.val < 479 then 157 else 139))))) else (if i.val < 496 then (if i.val < 488 then (if i.val < 484 then (if i.val < 482 then (if i.val < 481 then 72 else 169) else (if i.val < 483 then 48 else 173)) else (if i.val < 486 then (if i.val < 485 then 171 else 156) else (if i.val < 487 then 59 else 160))) else (if i.val < 492 then (if i.val < 490 then (if i.val < 489 then 157 else 143) else (if i.val < 491 then 169 else 165)) else (if i.val < 494 then (if i.val < 493 then 155 else 173) else (if i.val < 495 then 171 else 156)))) else (if i.val < 504 then (if i.val < 500 then (if i.val < 498 then (if i.val < 497 then 164 else 158) else (if i.val < 499 then 47 else 148)) else (if i.val < 502 then (if i.val < 501 then 133 else 46) else (if i.val < 503 then 39 else 38))) else (if i.val < 508 then (if i.val < 506 then (if i.val < 505 then 160 else 157) else (if i.val < 507 then 139 else 143)) else (if i.val < 510 then (if i.val < 509 then 74 else 182) else (if i.val < 511 then 180 else 174))))))))) else (if i.val < 768 then (if i.val < 640 then (if i.val < 576 then (if i.val < 544 then (if i.val < 528 then (if i.val < 520 then (if i.val < 516 then (if i.val < 514 then (if i.val < 513 then 178 else 180) else (if i.val < 515 then 151 else 8)) else (if i.val < 518 then (if i.val < 517 then 62 else 61) else (if i.val < 519 then 57 else 61))) else (if i.val < 524 then (if i.val < 522 then (if i.val < 521 then 41 else 78) else (if i.val < 523 then 76 else 77)) else (if i.val < 526 then (if i.val < 525 then 76 else 77) else (if i.val < 527 then 49 else 183)))) else (if i.val < 536 then (if i.val < 532 then (if i.val < 530 then (if i.val < 529 then 176 else 183) else (if i.val < 531 then 166 else 153)) else (if i.val < 534 then (if i.val < 533 then 183 else 172) else (if i.val < 535 then 154 else 183))) else (if i.val < 540 then (if i.val < 538 then (if i.val < 537 then 166 else 172) else (if i.val < 539 then 152 else 153)) else (if i.val < 542 then (if i.val < 541 then 154 else 170) else (if i.val < 543 then 177 else 56))))) else (if i.val < 560 then (if i.val < 552 then (if i.val < 548 then (if i.val < 546 then (if i.val < 545 then 176 else 163) else (if i.val < 547 then 78 else 170)) else (if i.val < 550 then (if i.val < 549 then 166 else 161) else (if i.val < 551 then 174 else 159))) else (if i.val < 556 then (if i.val < 554 then (if i.val < 553 then 163 else 140) else (if i.val < 555 then 78 else 170)) else (if i.val < 558 then (if i.val < 557 then 49 else 52) else (if i.val < 559 then 172 else 162)))) else (if i.val < 568 then (if i.val < 564 then (if i.val < 562 then (if i.val < 561 then 40 else 163) else (if i.val < 563 then 144 else 170)) else (if i.val < 566 then (if i.val < 565 then 166 else 161) else (if i.val < 567 then 52 else 172))) else (if i.val < 572 then (if i.val < 570 then (if i.val < 569 then 162 else 38) else (if i.val < 571 then 152 else 134)) else (if i.val < 574 then (if i.val < 573 then 159 else 158) else (if i.val < 575 then 40 else 163)))))) else (if i.val < 608 then (if i.val < 592 then (if i.val < 584 then (if i.val < 580 then (if i.val < 578 then (if i.val < 577 then 140 else 144) else (if i.val < 579 then 182 else 178)) else (if i.val < 582 then (if i.val < 581 then 151 else 175) else (if i.val < 583 then 149 else 148))) else (if i.val < 588 then (if i.val < 586 then (if i.val < 585 then 149 else 154) else (if i.val < 587 then 152 else 154)) else (if i.val < 590 then (if i.val < 589 then 62 else 57) else (if i.val < 591 then 41 else 56)))) else (if i.val < 600 then (if i.val < 596 then (if i.val < 594 then (if i.val < 593 then 50 else 50) else (if i.val < 595 then 38 else 168)) else (if i.val < 598 then (if i.val < 597 then 147 else 168) else (if i.val < 599 then 145 else 147))) else (if i.val < 604 then (if i.val < 602 then (if i.val < 601 then 138 else 168) else (if i.val < 603 then 146 else 147)) else (if i.val < 606 then (if i.val < 605 then 142 else 168) else (if i.val < 607 then 145 else 146))))) else (if i.val < 624 then (if i.val < 616 then (if i.val < 612 then (if i.val < 610 then (if i.val < 609 then 132 else 147) else (if i.val < 611 then 138 else 142)) else (if i.val < 614 then (if i.val < 613 then 136 else 177) else (if i.val < 615 then 175 else 141))) else (if i.val < 620 then (if i.val < 618 then (if i.val < 617 then 136 else 145) else (if i.val < 619 then 135 else 155)) else (if i.val < 622 then (if i.val < 621 then 139 else 141) else (if i.val < 623 then 136 else 162)))) else (if i.val < 632 then (if i.val < 628 then (if i.val < 626 then (if i.val < 625 then 146 else 137) else (if i.val < 627 then 144 else 141)) else (if i.val < 630 then (if i.val < 629 then 136 else 145) else (if i.val < 631 then 135 else 162))) else (if i.val < 636 then (if i.val < 634 then (if i.val < 633 then 146 else 137) else (if i.val < 635 then 152 else 134)) else (if i.val < 638 then (if i.val < 637 then 148 else 132) else (if i.val < 639 then 133 else 158))))))) else (if i.val < 704 then (if i.val < 672 then (if i.val < 656 then (if i.val < 648 then (if i.val < 644 then (if i.val < 642 then (if i.val < 641 then 155 else 139) else (if i.val < 643 then 144 else 141)) else (if i.val < 646 then (if i.val < 645 then 36 else 126) else (if i.val < 647 then 124 else 109))) else (if i.val < 652 then (if i.val < 650 then (if i.val < 649 then 115 else 124) else (if i.val < 651 then 90 else 33)) else (if i.val < 654 then (if i.val < 653 then 120 else 119) else (if i.val < 655 then 114 else 119)))) else (if i.val < 664 then (if i.val < 660 then (if i.val < 658 then (if i.val < 657 then 88 else 130) else (if i.val < 659 then 128 else 129)) else (if i.val < 662 then (if i.val < 661 then 128 else 129) else (if i.val < 663 then 100 else 225))) else (if i.val < 668 then (if i.val < 666 then (if i.val < 665 then 224 else 225) else (if i.val < 667 then 219 else 209)) else (if i.val < 670 then (if i.val < 669 then 225 else 223) else (if i.val < 671 then 210 else 225))))) else (if i.val < 688 then (if i.val < 680 then (if i.val < 676 then (if i.val < 674 then (if i.val < 673 then 219 else 223) else (if i.val < 675 then 208 else 209)) else (if i.val < 678 then (if i.val < 677 then 210 else 222) else (if i.val < 679 then 113 else 112))) else (if i.val < 684 then (if i.val < 682 then (if i.val < 681 then 224 else 217) else (if i.val < 683 then 130 else 222)) else (if i.val < 686 then (if i.val < 685 then 219 else 215) else (if i.val < 687 then 109 else 96)))) else (if i.val < 696 then (if i.val < 692 then (if i.val < 690 then (if i.val < 689 then 217 else 197) else (if i.val < 691 then 130 else 222)) else (if i.val < 694 then (if i.val < 693 then 100 else 106) else (if i.val < 695 then 223 else 216))) else (if i.val < 700 then (if i.val < 698 then (if i.val < 697 then 93 else 217) else (if i.val < 699 then 203 else 222)) else (if i.val < 702 then (if i.val < 701 then 219 else 215) else (if i.val < 703 then 106 else 223)))))) else (if i.val < 736 then (if i.val < 720 then (if i.val < 712 then (if i.val < 708 then (if i.val < 706 then (if i.val < 705 then 216 else 91) else (if i.val < 707 then 208 else 187)) else (if i.val < 710 then (if i.val < 709 then 96 else 95) else (if i.val < 711 then 93 else 217))) else (if i.val < 716 then (if i.val < 714 then (if i.val < 713 then 197 else 203) else (if i.val < 715 then 126 else 115)) else (if i.val < 718 then (if i.val < 717 then 90 else 111) else (if i.val < 719 then 86 else 85)))) else (if i.val < 728 then (if i.val < 724 then (if i.val < 722 then (if i.val < 721 then 86 else 210) else (if i.val < 723 then 208 else 210)) else (if i.val < 726 then (if i.val < 725 then 120 else 114) else (if i.val < 727 then 88 else 112))) else (if i.val < 732 then (if i.val < 730 then (if i.val < 729 then 102 else 102) else (if i.val < 731 then 91 else 220)) else (if i.val < 734 then (if i.val < 733 then 207 else 220) else (if i.val < 735 then 205 else 207))))) else (if i.val < 752 then (if i.val < 744 then (if i.val < 740 then (if i.val < 738 then (if i.val < 737 then 195 else 220) else (if i.val < 739 then 206 else 207)) else (if i.val < 742 then (if i.val < 741 then 201 else 220) else (if i.val < 743 then 205 else 206))) else (if i.val < 748 then (if i.val < 746 then (if i.val < 745 then 185 else 207) else (if i.val < 747 then 195 else 201)) else (if i.val < 750 then (if i.val < 749 then 214 else 113) else (if i.val < 751 then 111 else 199)))) else (if i.val < 760 then (if i.val < 756 then (if i.val < 754 then (if i.val < 753 then 214 else 205) else (if i.val < 755 then 189 else 80)) else (if i.val < 758 then (if i.val < 757 then 82 else 199) else (if i.val < 759 then 214 else 216))) else (if i.val < 764 then (if i.val < 762 then (if i.val < 761 then 206 else 193) else (if i.val < 763 then 203 else 199)) else (if i.val < 766 then (if i.val < 765 then 214 else 205) else (if i.val < 767 then 189 else 216)))))))) else (if i.val < 896 then (if i.val < 832 then (if i.val < 800 then (if i.val < 784 then (if i.val < 776 then (if i.val < 772 then (if i.val < 770 then (if i.val < 769 then 206 else 193) else (if i.val < 771 then 208 else 187)) else (if i.val < 774 then (if i.val < 773 then 85 else 185) else (if i.val < 775 then 79 else 95))) else (if i.val < 780 then (if i.val < 778 then (if i.val < 777 then 80 else 82) else (if i.val < 779 then 203 else 199)) else (if i.val < 782 then (if i.val < 781 then 224 else 209) else (if i.val < 783 then 209 else 87)))) else (if i.val < 792 then (if i.val < 788 then (if i.val < 786 then (if i.val < 785 then 87 else 103) else (if i.val < 787 then 103 else 221)) else (if i.val < 790 then (if i.val < 789 then 213 else 221) else (if i.val < 791 then 211 else 213))) else (if i.val < 796 then (if i.val < 794 then (if i.val < 793 then 196 else 221) else (if i.val < 795 then 212 else 213)) else (if i.val < 798 then (if i.val < 797 then 202 else 221) else (if i.val < 799 then 211 else 212))))) else (if i.val < 816 then (if i.val < 808 then (if i.val < 804 then (if i.val < 802 then (if i.val < 801 then 186 else 213) else (if i.val < 803 then 196 else 202)) else (if i.val < 806 then (if i.val < 805 then 218 else 224) else (if i.val < 807 then 200 else 218))) else (if i.val < 812 then (if i.val < 810 then (if i.val < 809 then 211 else 190) else (if i.val < 811 then 215 else 197)) else (if i.val < 814 then (if i.val < 813 then 200 else 218) else (if i.val < 815 then 81 else 212)))) else (if i.val < 824 then (if i.val < 820 then (if i.val < 818 then (if i.val < 817 then 194 else 84) else (if i.val < 819 then 200 else 218)) else (if i.val < 822 then (if i.val < 821 then 211 else 190) else (if i.val < 823 then 81 else 212))) else (if i.val < 828 then (if i.val < 826 then (if i.val < 825 then 194 else 79) else (if i.val < 827 then 186 else 187)) else (if i.val < 830 then (if i.val < 829 then 215 else 197) else (if i.val < 831 then 84 else 200)))))) else (if i.val < 864 then (if i.val < 848 then (if i.val < 840 then (if i.val < 836 then (if i.val < 834 then (if i.val < 833 then 195 else 185) else (if i.val < 835 then 195 else 202)) else (if i.val < 838 then (if i.val < 837 then 186 else 202) else (if i.val < 839 then 79 else 204))) else (if i.val < 844 then (if i.val < 842 then (if i.val < 841 then 198 else 204) else (if i.val < 843 then 188 else 198)) else (if i.val < 846 then (if i.val < 845 then 204 else 192) else (if i.val < 847 then 198 else 204)))) else (if i.val < 856 then (if i.val < 852 then (if i.val < 850 then (if i.val < 849 then 188 else 192) else (if i.val < 851 then 198 else 191)) else (if i.val < 854 then (if i.val < 853 then 191 else 188) else (if i.val < 855 then 189 else 191))) else (if i.val < 860 then (if i.val < 858 then (if i.val < 857 then 194 else 192) else (if i.val < 859 then 191 else 188)) else (if i.val < 862 then (if i.val < 861 then 189 else 194) else (if i.val < 863 then 192 else 186))))) else (if i.val < 880 then (if i.val < 872 then (if i.val < 868 then (if i.val < 866 then (if i.val < 865 then 187 else 185) else (if i.val < 867 then 176 else 153)) else (if i.val < 870 then (if i.val < 869 then 153 else 150) else (if i.val < 871 then 150 else 167))) else (if i.val < 876 then (if i.val < 874 then (if i.val < 873 then 167 else 247) else (if i.val < 875 then 244 else 247)) else (if i.val < 878 then (if i.val < 877 then 242 else 244) else (if i.val < 879 then 236 else 247)))) else (if i.val < 888 then (if i.val < 884 then (if i.val < 882 then (if i.val < 881 then 243 else 244) else (if i.val < 883 then 240 else 247)) else (if i.val < 886 then (if i.val < 885 then 242 else 243) else (if i.val < 887 then 226 else 244))) else (if i.val < 892 then (if i.val < 890 then (if i.val < 889 then 236 else 240) else (if i.val < 891 then 246 else 176)) else (if i.val < 894 then (if i.val < 893 then 239 else 246) else (if i.val < 895 then 242 else 229))))))) else (if i.val < 960 then (if i.val < 928 then (if i.val < 912 then (if i.val < 904 then (if i.val < 900 then (if i.val < 898 then (if i.val < 897 then 161 else 140) else (if i.val < 899 then 239 else 246)) else (if i.val < 902 then (if i.val < 901 then 156 else 243) else (if i.val < 903 then 235 else 143))) else (if i.val < 908 then (if i.val < 906 then (if i.val < 905 then 239 else 246) else (if i.val < 907 then 242 else 229)) else (if i.val < 910 then (if i.val < 909 then 156 else 243) else (if i.val < 911 then 235 else 133)))) else (if i.val < 920 then (if i.val < 916 then (if i.val < 914 then (if i.val < 913 then 226 else 134) else (if i.val < 915 then 161 else 140)) else (if i.val < 918 then (if i.val < 917 then 143 else 239) else (if i.val < 919 then 138 else 132))) else (if i.val < 924 then (if i.val < 922 then (if i.val < 921 then 138 else 240) else (if i.val < 923 then 226 else 240)) else (if i.val < 926 then (if i.val < 925 then 133 else 241) else (if i.val < 927 then 237 else 241))))) else (if i.val < 944 then (if i.val < 936 then (if i.val < 932 then (if i.val < 930 then (if i.val < 929 then 227 else 237) else (if i.val < 931 then 241 else 233)) else (if i.val < 934 then (if i.val < 933 then 237 else 241) else (if i.val < 935 then 227 else 233))) else (if i.val < 940 then (if i.val < 938 then (if i.val < 937 then 237 else 231) else (if i.val < 939 then 231 else 227)) else (if i.val < 942 then (if i.val < 941 then 135 else 231) else (if i.val < 943 then 235 else 233)))) else (if i.val < 952 then (if i.val < 948 then (if i.val < 946 then (if i.val < 945 then 231 else 227) else (if i.val < 947 then 135 else 235)) else (if i.val < 950 then (if i.val < 949 then 233 else 226) else (if i.val < 951 then 134 else 132))) else (if i.val < 956 then (if i.val < 954 then (if i.val < 953 then 236 else 236) else (if i.val < 955 then 142 else 142)) else (if i.val < 958 then (if i.val < 957 then 245 else 238) else (if i.val < 959 then 245 else 228)))))) else (if i.val < 992 then (if i.val < 976 then (if i.val < 968 then (if i.val < 964 then (if i.val < 962 then (if i.val < 961 then 238 else 245) else (if i.val < 963 then 234 else 238)) else (if i.val < 966 then (if i.val < 965 then 245 else 228) else (if i.val < 967 then 234 else 238))) else (if i.val < 972 then (if i.val < 970 then (if i.val < 969 then 232 else 232) else (if i.val < 971 then 228 else 229)) else (if i.val < 974 then (if i.val < 973 then 232 else 137) else (if i.val < 975 then 234 else 232)))) else (if i.val < 984 then (if i.val < 980 then (if i.val < 978 then (if i.val < 977 then 228 else 229) else (if i.val < 979 then 137 else 234)) else (if i.val < 982 then (if i.val < 981 then 230 else 230) else (if i.val < 983 then 230 else 230))) else (if i.val < 988 then (if i.val < 986 then (if i.val < 985 then 196 else 196) else (if i.val < 987 then 201 else 201)) else (if i.val < 990 then (if i.val < 989 then 254 else 253) else (if i.val < 991 then 254 else 248))))) else (if i.val < 1008 then (if i.val < 1000 then (if i.val < 996 then (if i.val < 994 then (if i.val < 993 then 253 else 254) else (if i.val < 995 then 252 else 253)) else (if i.val < 998 then (if i.val < 997 then 254 else 248) else (if i.val < 999 then 252 else 253))) else (if i.val < 1004 then (if i.val < 1002 then (if i.val < 1001 then 251 else 251) else (if i.val < 1003 then 248 else 190)) else (if i.val < 1006 then (if i.val < 1005 then 251 else 193) else (if i.val < 1007 then 252 else 251)))) else (if i.val < 1016 then (if i.val < 1012 then (if i.val < 1010 then (if i.val < 1009 then 248 else 190) else (if i.val < 1011 then 193 else 252)) else (if i.val < 1014 then (if i.val < 1013 then 249 else 249) else (if i.val < 1015 then 249 else 249))) else (if i.val < 1020 then (if i.val < 1018 then (if i.val < 1017 then 250 else 250) else (if i.val < 1019 then 250 else 250)) else (if i.val < 1022 then (if i.val < 1021 then 255 else 255) else (if i.val < 1023 then 255 else 255)))))))))))
    (fun j => (if j.val < 128 then (if j.val < 64 then (if j.val < 32 then (if j.val < 16 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 4) else (if j.val < 3 then 3 else 1)) else (if j.val < 6 then (if j.val < 5 then 2 else 17) else (if j.val < 7 then 16 else 14))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 15 else 13) else (if j.val < 11 then 6 else 8)) else (if j.val < 14 then (if j.val < 13 then 7 else 5) else (if j.val < 15 then 9 else 57)))) else (if j.val < 24 then (if j.val < 20 then (if j.val < 18 then (if j.val < 17 then 46 else 27) else (if j.val < 19 then 35 else 54)) else (if j.val < 22 then (if j.val < 21 then 48 else 50) else (if j.val < 23 then 49 else 47))) else (if j.val < 28 then (if j.val < 26 then (if j.val < 25 then 51 else 45) else (if j.val < 27 then 43 else 44)) else (if j.val < 30 then (if j.val < 29 then 23 else 18) else (if j.val < 31 then 31 else 26))))) else (if j.val < 48 then (if j.val < 40 then (if j.val < 36 then (if j.val < 34 then (if j.val < 33 then 24 else 25) else (if j.val < 35 then 19 else 34)) else (if j.val < 38 then (if j.val < 37 then 32 else 33) else (if j.val < 39 then 155 else 141))) else (if j.val < 44 then (if j.val < 42 then (if j.val < 41 then 147 else 132) else (if j.val < 43 then 76 else 96)) else (if j.val < 46 then (if j.val < 45 then 87 else 65) else (if j.val < 47 then 107 else 131)))) else (if j.val < 56 then (if j.val < 52 then (if j.val < 50 then (if j.val < 49 then 84 else 104) else (if j.val < 51 then 137 else 133)) else (if j.val < 54 then (if j.val < 53 then 144 else 126) else (if j.val < 55 then 79 else 99))) else (if j.val < 60 then (if j.val < 58 then (if j.val < 57 then 134 else 128) else (if j.val < 59 then 81 else 101)) else (if j.val < 62 then (if j.val < 61 then 125 else 127) else (if j.val < 63 then 124 else 75)))))) else (if j.val < 96 then (if j.val < 80 then (if j.val < 72 then (if j.val < 68 then (if j.val < 66 then (if j.val < 65 then 73 else 74) else (if j.val < 67 then 61 else 95)) else (if j.val < 70 then (if j.val < 69 then 93 else 94) else (if j.val < 71 then 78 else 80))) else (if j.val < 76 then (if j.val < 74 then (if j.val < 73 then 77 else 64) else (if j.val < 75 then 62 else 63)) else (if j.val < 78 then (if j.val < 77 then 98 else 100) else (if j.val < 79 then 97 else 363)))) else (if j.val < 88 then (if j.val < 84 then (if j.val < 82 then (if j.val < 81 then 337 else 348) else (if j.val < 83 then 342 else 333)) else (if j.val < 86 then (if j.val < 85 then 352 else 326) else (if j.val < 87 then 319 else 322))) else (if j.val < 92 then (if j.val < 90 then (if j.val < 89 then 205 else 169) else (if j.val < 91 then 255 else 228)) else (if j.val < 94 then (if j.val < 93 then 214 else 220) else (if j.val < 95 then 180 else 278))))) else (if j.val < 112 then (if j.val < 104 then (if j.val < 100 then (if j.val < 98 then (if j.val < 97 then 264 else 270) else (if j.val < 99 then 204 else 254)) else (if j.val < 102 then (if j.val < 101 then 177 else 318) else (if j.val < 103 then 210 else 260))) else (if j.val < 108 then (if j.val < 106 then (if j.val < 105 then 329 else 321) else (if j.val < 107 then 217 else 267)) else (if j.val < 110 then (if j.val < 109 then 199 else 249) else (if j.val < 111 then 172 else 316)))) else (if j.val < 120 then (if j.val < 116 then (if j.val < 114 then (if j.val < 113 then 207 else 257) else (if j.val < 115 then 201 else 251)) else (if j.val < 118 then (if j.val < 117 then 174 else 315) else (if j.val < 119 then 198 else 200))) else (if j.val < 124 then (if j.val < 122 then (if j.val < 121 then 197 else 168) else (if j.val < 123 then 166 else 167)) else (if j.val < 126 then (if j.val < 125 then 248 else 250) else (if j.val < 127 then 247 else 206))))))) else (if j.val < 192 then (if j.val < 160 then (if j.val < 144 then (if j.val < 136 then (if j.val < 132 then (if j.val < 130 then (if j.val < 129 then 171 else 173) else (if j.val < 131 then 170 else 256)) else (if j.val < 134 then (if j.val < 133 then 608 else 500) else (if j.val < 135 then 571 else 618))) else (if j.val < 140 then (if j.val < 138 then (if j.val < 137 then 612 else 625) else (if j.val < 139 then 600 else 479)) else (if j.val < 142 then (if j.val < 141 then 553 else 615) else (if j.val < 143 then 604 else 489)))) else (if j.val < 152 then (if j.val < 148 then (if j.val < 146 then (if j.val < 145 then 562 else 598) else (if j.val < 147 then 602 else 596)) else (if j.val < 150 then (if j.val < 149 then 463 else 456) else (if j.val < 151 then 459 else 392))) else (if j.val < 156 then (if j.val < 154 then (if j.val < 153 then 538 else 531) else (if j.val < 155 then 534 else 474)) else (if j.val < 158 then (if j.val < 157 then 485 else 470) else (if j.val < 159 then 415 else 401))))) else (if j.val < 176 then (if j.val < 168 then (if j.val < 164 then (if j.val < 162 then (if j.val < 161 then 407 else 549) else (if j.val < 163 then 559 else 545)) else (if j.val < 166 then (if j.val < 165 then 391 else 455) else (if j.val < 167 then 530 else 397))) else (if j.val < 172 then (if j.val < 170 then (if j.val < 169 then 595 else 466) else (if j.val < 171 then 541 else 458)) else (if j.val < 174 then (if j.val < 173 then 533 else 404) else (if j.val < 175 then 386 else 453)))) else (if j.val < 184 then (if j.val < 180 then (if j.val < 178 then (if j.val < 177 then 528 else 394) else (if j.val < 179 then 388 else 452)) else (if j.val < 182 then (if j.val < 181 then 385 else 387) else (if j.val < 183 then 384 else 527))) else (if j.val < 188 then (if j.val < 186 then (if j.val < 185 then 393 else 744) else (if j.val < 187 then 800 else 707)) else (if j.val < 190 then (if j.val < 189 then 842 else 754) else (if j.val < 191 then 809 else 851)))))) else (if j.val < 224 then (if j.val < 208 then (if j.val < 200 then (if j.val < 196 then (if j.val < 194 then (if j.val < 193 then 845 else 761) else (if j.val < 195 then 816 else 736)) else (if j.val < 198 then (if j.val < 197 then 792 else 689) else (if j.val < 199 then 840 else 751))) else (if j.val < 204 then (if j.val < 202 then (if j.val < 201 then 806 else 740) else (if j.val < 203 then 796 else 698)) else (if j.val < 206 then (if j.val < 205 then 839 else 734) else (if j.val < 207 then 738 else 732)))) else (if j.val < 216 then (if j.val < 212 then (if j.val < 210 then (if j.val < 209 then 674 else 667) else (if j.val < 211 then 670 else 790)) else (if j.val < 214 then (if j.val < 213 then 794 else 788) else (if j.val < 215 then 748 else 685))) else (if j.val < 220 then (if j.val < 218 then (if j.val < 217 then 695 else 681) else (if j.val < 219 then 804 else 666)) else (if j.val < 222 then (if j.val < 221 then 731 else 787) else (if j.val < 223 then 677 else 669))))) else (if j.val < 240 then (if j.val < 232 then (if j.val < 228 then (if j.val < 226 then (if j.val < 225 then 664 else 663) else (if j.val < 227 then 886 else 928)) else (if j.val < 230 then (if j.val < 229 then 959 else 895) else (if j.val < 231 then 980 else 937))) else (if j.val < 236 then (if j.val < 234 then (if j.val < 233 then 968 else 931) else (if j.val < 235 then 962 else 902)) else (if j.val < 238 then (if j.val < 237 then 878 else 926) else (if j.val < 239 then 957 else 892)))) else (if j.val < 248 then (if j.val < 244 then (if j.val < 242 then (if j.val < 241 then 882 else 925) else (if j.val < 243 then 876 else 880)) else (if j.val < 246 then (if j.val < 245 then 874 else 956) else (if j.val < 247 then 890 else 873))) else (if j.val < 252 then (if j.val < 250 then (if j.val < 249 then 991 else 1012) else (if j.val < 251 then 1016 else 1000)) else (if j.val < 254 then (if j.val < 253 then 994 else 989) else (if j.val < 255 then 988 else 1020)))))))))
    (Fin.addCases (m := 512) (n := 512) (Fin.addCases (m := 256) (n := 256) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)))) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))))) (Fin.addCases (m := 256) (n := 256) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)))) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)))))) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))))

theorem alpha_kernel : alphaCertificate.hom.ker.map
    (Subgroup.closure (Set.range alphaGenerators)).subtype =
      Subgroup.closure (Set.range axisGenerators) :=
  alphaCertificate.kernel_image_eq_of_rows axisCertificate
    (fun i => (if i.val < 512 then (if i.val < 256 then (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 0) else (if i.val < 7 then 0 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 0) else (if i.val < 11 then 0 else 0)) else (if i.val < 14 then (if i.val < 13 then 3 else 0) else (if i.val < 15 then 0 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 0) else (if i.val < 19 then 0 else 0)) else (if i.val < 22 then (if i.val < 21 then 0 else 0) else (if i.val < 23 then 0 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 0) else (if i.val < 27 then 0 else 0)) else (if i.val < 30 then (if i.val < 29 then 0 else 0) else (if i.val < 31 then 0 else 0))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 0 else 0) else (if i.val < 35 then 0 else 0)) else (if i.val < 38 then (if i.val < 37 then 0 else 0) else (if i.val < 39 then 0 else 0))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 0 else 0) else (if i.val < 43 then 0 else 0)) else (if i.val < 46 then (if i.val < 45 then 0 else 0) else (if i.val < 47 then 0 else 0)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 0 else 0) else (if i.val < 51 then 0 else 0)) else (if i.val < 54 then (if i.val < 53 then 0 else 0) else (if i.val < 55 then 0 else 0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 0 else 0) else (if i.val < 59 then 0 else 0)) else (if i.val < 62 then (if i.val < 61 then 0 else 0) else (if i.val < 63 then 0 else 0)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 0 else 0) else (if i.val < 67 then 0 else 2)) else (if i.val < 70 then (if i.val < 69 then 0 else 0) else (if i.val < 71 then 0 else 0))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 0 else 0) else (if i.val < 75 then 0 else 0)) else (if i.val < 78 then (if i.val < 77 then 0 else 0) else (if i.val < 79 then 0 else 0)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 0 else 0) else (if i.val < 83 then 0 else 0)) else (if i.val < 86 then (if i.val < 85 then 0 else 0) else (if i.val < 87 then 0 else 0))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 0 else 0) else (if i.val < 91 then 1 else 0)) else (if i.val < 94 then (if i.val < 93 then 0 else 0) else (if i.val < 95 then 0 else 0))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 0 else 0) else (if i.val < 99 then 0 else 0)) else (if i.val < 102 then (if i.val < 101 then 0 else 0) else (if i.val < 103 then 0 else 0))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 0 else 0) else (if i.val < 107 then 0 else 0)) else (if i.val < 110 then (if i.val < 109 then 0 else 0) else (if i.val < 111 then 0 else 0)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 0 else 0) else (if i.val < 115 then 0 else 0)) else (if i.val < 118 then (if i.val < 117 then 0 else 0) else (if i.val < 119 then 0 else 0))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 0 else 0) else (if i.val < 123 then 0 else 0)) else (if i.val < 126 then (if i.val < 125 then 0 else 0) else (if i.val < 127 then 0 else 0))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 0 else 0) else (if i.val < 131 then 0 else 0)) else (if i.val < 134 then (if i.val < 133 then 0 else 0) else (if i.val < 135 then 0 else 0))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 0 else 0) else (if i.val < 139 then 0 else 0)) else (if i.val < 142 then (if i.val < 141 then 0 else 0) else (if i.val < 143 then 0 else 0)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 0 else 0) else (if i.val < 147 then 0 else 0)) else (if i.val < 150 then (if i.val < 149 then 0 else 0) else (if i.val < 151 then 0 else 0))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 0 else 0) else (if i.val < 155 then 0 else 0)) else (if i.val < 158 then (if i.val < 157 then 0 else 0) else (if i.val < 159 then 0 else 0))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 0 else 0) else (if i.val < 163 then 0 else 0)) else (if i.val < 166 then (if i.val < 165 then 0 else 0) else (if i.val < 167 then 0 else 0))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 0 else 0) else (if i.val < 171 then 0 else 0)) else (if i.val < 174 then (if i.val < 173 then 0 else 0) else (if i.val < 175 then 0 else 0)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 0 else 0) else (if i.val < 179 then 0 else 0)) else (if i.val < 182 then (if i.val < 181 then 0 else 0) else (if i.val < 183 then 0 else 0))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 0 else 0) else (if i.val < 187 then 0 else 0)) else (if i.val < 190 then (if i.val < 189 then 0 else 0) else (if i.val < 191 then 0 else 0)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 0 else 0) else (if i.val < 195 then 0 else 0)) else (if i.val < 198 then (if i.val < 197 then 0 else 0) else (if i.val < 199 then 0 else 0))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 0 else 0) else (if i.val < 203 then 0 else 0)) else (if i.val < 206 then (if i.val < 205 then 0 else 0) else (if i.val < 207 then 0 else 0)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 0 else 0) else (if i.val < 211 then 0 else 0)) else (if i.val < 214 then (if i.val < 213 then 0 else 0) else (if i.val < 215 then 0 else 0))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 0 else 0) else (if i.val < 219 then 0 else 0)) else (if i.val < 222 then (if i.val < 221 then 0 else 0) else (if i.val < 223 then 0 else 0))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 0 else 0) else (if i.val < 227 then 0 else 0)) else (if i.val < 230 then (if i.val < 229 then 0 else 0) else (if i.val < 231 then 0 else 0))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 0 else 0) else (if i.val < 235 then 0 else 0)) else (if i.val < 238 then (if i.val < 237 then 0 else 0) else (if i.val < 239 then 0 else 0)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 0 else 0) else (if i.val < 243 then 0 else 0)) else (if i.val < 246 then (if i.val < 245 then 0 else 0) else (if i.val < 247 then 0 else 0))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 0 else 0) else (if i.val < 251 then 0 else 0)) else (if i.val < 254 then (if i.val < 253 then 0 else 0) else (if i.val < 255 then 0 else 0)))))))) else (if i.val < 384 then (if i.val < 320 then (if i.val < 288 then (if i.val < 272 then (if i.val < 264 then (if i.val < 260 then (if i.val < 258 then (if i.val < 257 then 0 else 0) else (if i.val < 259 then 0 else 0)) else (if i.val < 262 then (if i.val < 261 then 0 else 0) else (if i.val < 263 then 0 else 0))) else (if i.val < 268 then (if i.val < 266 then (if i.val < 265 then 0 else 0) else (if i.val < 267 then 0 else 0)) else (if i.val < 270 then (if i.val < 269 then 0 else 0) else (if i.val < 271 then 0 else 0)))) else (if i.val < 280 then (if i.val < 276 then (if i.val < 274 then (if i.val < 273 then 0 else 0) else (if i.val < 275 then 0 else 0)) else (if i.val < 278 then (if i.val < 277 then 0 else 0) else (if i.val < 279 then 0 else 0))) else (if i.val < 284 then (if i.val < 282 then (if i.val < 281 then 0 else 0) else (if i.val < 283 then 0 else 0)) else (if i.val < 286 then (if i.val < 285 then 0 else 0) else (if i.val < 287 then 0 else 0))))) else (if i.val < 304 then (if i.val < 296 then (if i.val < 292 then (if i.val < 290 then (if i.val < 289 then 0 else 0) else (if i.val < 291 then 0 else 0)) else (if i.val < 294 then (if i.val < 293 then 0 else 0) else (if i.val < 295 then 0 else 0))) else (if i.val < 300 then (if i.val < 298 then (if i.val < 297 then 0 else 0) else (if i.val < 299 then 0 else 0)) else (if i.val < 302 then (if i.val < 301 then 0 else 0) else (if i.val < 303 then 0 else 0)))) else (if i.val < 312 then (if i.val < 308 then (if i.val < 306 then (if i.val < 305 then 0 else 0) else (if i.val < 307 then 0 else 0)) else (if i.val < 310 then (if i.val < 309 then 0 else 0) else (if i.val < 311 then 0 else 0))) else (if i.val < 316 then (if i.val < 314 then (if i.val < 313 then 0 else 0) else (if i.val < 315 then 0 else 0)) else (if i.val < 318 then (if i.val < 317 then 0 else 0) else (if i.val < 319 then 0 else 0)))))) else (if i.val < 352 then (if i.val < 336 then (if i.val < 328 then (if i.val < 324 then (if i.val < 322 then (if i.val < 321 then 0 else 0) else (if i.val < 323 then 0 else 0)) else (if i.val < 326 then (if i.val < 325 then 0 else 0) else (if i.val < 327 then 0 else 0))) else (if i.val < 332 then (if i.val < 330 then (if i.val < 329 then 0 else 0) else (if i.val < 331 then 0 else 0)) else (if i.val < 334 then (if i.val < 333 then 0 else 0) else (if i.val < 335 then 0 else 0)))) else (if i.val < 344 then (if i.val < 340 then (if i.val < 338 then (if i.val < 337 then 0 else 0) else (if i.val < 339 then 0 else 0)) else (if i.val < 342 then (if i.val < 341 then 0 else 0) else (if i.val < 343 then 0 else 0))) else (if i.val < 348 then (if i.val < 346 then (if i.val < 345 then 0 else 0) else (if i.val < 347 then 0 else 0)) else (if i.val < 350 then (if i.val < 349 then 0 else 0) else (if i.val < 351 then 0 else 0))))) else (if i.val < 368 then (if i.val < 360 then (if i.val < 356 then (if i.val < 354 then (if i.val < 353 then 0 else 0) else (if i.val < 355 then 0 else 0)) else (if i.val < 358 then (if i.val < 357 then 0 else 0) else (if i.val < 359 then 0 else 0))) else (if i.val < 364 then (if i.val < 362 then (if i.val < 361 then 0 else 0) else (if i.val < 363 then 0 else 0)) else (if i.val < 366 then (if i.val < 365 then 0 else 0) else (if i.val < 367 then 0 else 0)))) else (if i.val < 376 then (if i.val < 372 then (if i.val < 370 then (if i.val < 369 then 0 else 0) else (if i.val < 371 then 0 else 0)) else (if i.val < 374 then (if i.val < 373 then 0 else 0) else (if i.val < 375 then 0 else 0))) else (if i.val < 380 then (if i.val < 378 then (if i.val < 377 then 0 else 0) else (if i.val < 379 then 0 else 0)) else (if i.val < 382 then (if i.val < 381 then 0 else 0) else (if i.val < 383 then 0 else 0))))))) else (if i.val < 448 then (if i.val < 416 then (if i.val < 400 then (if i.val < 392 then (if i.val < 388 then (if i.val < 386 then (if i.val < 385 then 0 else 0) else (if i.val < 387 then 0 else 0)) else (if i.val < 390 then (if i.val < 389 then 0 else 0) else (if i.val < 391 then 0 else 0))) else (if i.val < 396 then (if i.val < 394 then (if i.val < 393 then 0 else 0) else (if i.val < 395 then 0 else 0)) else (if i.val < 398 then (if i.val < 397 then 0 else 0) else (if i.val < 399 then 0 else 0)))) else (if i.val < 408 then (if i.val < 404 then (if i.val < 402 then (if i.val < 401 then 0 else 0) else (if i.val < 403 then 0 else 0)) else (if i.val < 406 then (if i.val < 405 then 0 else 0) else (if i.val < 407 then 0 else 0))) else (if i.val < 412 then (if i.val < 410 then (if i.val < 409 then 0 else 0) else (if i.val < 411 then 0 else 0)) else (if i.val < 414 then (if i.val < 413 then 0 else 0) else (if i.val < 415 then 0 else 0))))) else (if i.val < 432 then (if i.val < 424 then (if i.val < 420 then (if i.val < 418 then (if i.val < 417 then 0 else 0) else (if i.val < 419 then 0 else 0)) else (if i.val < 422 then (if i.val < 421 then 0 else 0) else (if i.val < 423 then 0 else 0))) else (if i.val < 428 then (if i.val < 426 then (if i.val < 425 then 0 else 0) else (if i.val < 427 then 0 else 0)) else (if i.val < 430 then (if i.val < 429 then 0 else 0) else (if i.val < 431 then 0 else 0)))) else (if i.val < 440 then (if i.val < 436 then (if i.val < 434 then (if i.val < 433 then 0 else 0) else (if i.val < 435 then 0 else 0)) else (if i.val < 438 then (if i.val < 437 then 0 else 0) else (if i.val < 439 then 0 else 0))) else (if i.val < 444 then (if i.val < 442 then (if i.val < 441 then 0 else 0) else (if i.val < 443 then 0 else 0)) else (if i.val < 446 then (if i.val < 445 then 0 else 0) else (if i.val < 447 then 0 else 0)))))) else (if i.val < 480 then (if i.val < 464 then (if i.val < 456 then (if i.val < 452 then (if i.val < 450 then (if i.val < 449 then 0 else 0) else (if i.val < 451 then 0 else 0)) else (if i.val < 454 then (if i.val < 453 then 0 else 0) else (if i.val < 455 then 0 else 0))) else (if i.val < 460 then (if i.val < 458 then (if i.val < 457 then 0 else 0) else (if i.val < 459 then 0 else 0)) else (if i.val < 462 then (if i.val < 461 then 0 else 0) else (if i.val < 463 then 0 else 0)))) else (if i.val < 472 then (if i.val < 468 then (if i.val < 466 then (if i.val < 465 then 0 else 0) else (if i.val < 467 then 0 else 0)) else (if i.val < 470 then (if i.val < 469 then 0 else 0) else (if i.val < 471 then 0 else 0))) else (if i.val < 476 then (if i.val < 474 then (if i.val < 473 then 0 else 0) else (if i.val < 475 then 0 else 0)) else (if i.val < 478 then (if i.val < 477 then 0 else 0) else (if i.val < 479 then 0 else 0))))) else (if i.val < 496 then (if i.val < 488 then (if i.val < 484 then (if i.val < 482 then (if i.val < 481 then 0 else 0) else (if i.val < 483 then 0 else 0)) else (if i.val < 486 then (if i.val < 485 then 0 else 0) else (if i.val < 487 then 0 else 0))) else (if i.val < 492 then (if i.val < 490 then (if i.val < 489 then 0 else 0) else (if i.val < 491 then 0 else 0)) else (if i.val < 494 then (if i.val < 493 then 0 else 0) else (if i.val < 495 then 0 else 0)))) else (if i.val < 504 then (if i.val < 500 then (if i.val < 498 then (if i.val < 497 then 0 else 0) else (if i.val < 499 then 0 else 0)) else (if i.val < 502 then (if i.val < 501 then 0 else 0) else (if i.val < 503 then 0 else 0))) else (if i.val < 508 then (if i.val < 506 then (if i.val < 505 then 0 else 0) else (if i.val < 507 then 0 else 0)) else (if i.val < 510 then (if i.val < 509 then 0 else 0) else (if i.val < 511 then 0 else 0))))))))) else (if i.val < 768 then (if i.val < 640 then (if i.val < 576 then (if i.val < 544 then (if i.val < 528 then (if i.val < 520 then (if i.val < 516 then (if i.val < 514 then (if i.val < 513 then 0 else 0) else (if i.val < 515 then 0 else 0)) else (if i.val < 518 then (if i.val < 517 then 0 else 0) else (if i.val < 519 then 0 else 0))) else (if i.val < 524 then (if i.val < 522 then (if i.val < 521 then 0 else 0) else (if i.val < 523 then 0 else 0)) else (if i.val < 526 then (if i.val < 525 then 0 else 0) else (if i.val < 527 then 0 else 0)))) else (if i.val < 536 then (if i.val < 532 then (if i.val < 530 then (if i.val < 529 then 0 else 0) else (if i.val < 531 then 0 else 0)) else (if i.val < 534 then (if i.val < 533 then 0 else 0) else (if i.val < 535 then 0 else 0))) else (if i.val < 540 then (if i.val < 538 then (if i.val < 537 then 0 else 0) else (if i.val < 539 then 0 else 0)) else (if i.val < 542 then (if i.val < 541 then 0 else 0) else (if i.val < 543 then 0 else 0))))) else (if i.val < 560 then (if i.val < 552 then (if i.val < 548 then (if i.val < 546 then (if i.val < 545 then 0 else 0) else (if i.val < 547 then 0 else 0)) else (if i.val < 550 then (if i.val < 549 then 0 else 0) else (if i.val < 551 then 0 else 0))) else (if i.val < 556 then (if i.val < 554 then (if i.val < 553 then 0 else 0) else (if i.val < 555 then 0 else 0)) else (if i.val < 558 then (if i.val < 557 then 0 else 0) else (if i.val < 559 then 0 else 0)))) else (if i.val < 568 then (if i.val < 564 then (if i.val < 562 then (if i.val < 561 then 0 else 0) else (if i.val < 563 then 0 else 0)) else (if i.val < 566 then (if i.val < 565 then 0 else 0) else (if i.val < 567 then 0 else 0))) else (if i.val < 572 then (if i.val < 570 then (if i.val < 569 then 0 else 0) else (if i.val < 571 then 0 else 0)) else (if i.val < 574 then (if i.val < 573 then 0 else 0) else (if i.val < 575 then 0 else 0)))))) else (if i.val < 608 then (if i.val < 592 then (if i.val < 584 then (if i.val < 580 then (if i.val < 578 then (if i.val < 577 then 0 else 0) else (if i.val < 579 then 0 else 0)) else (if i.val < 582 then (if i.val < 581 then 0 else 0) else (if i.val < 583 then 0 else 0))) else (if i.val < 588 then (if i.val < 586 then (if i.val < 585 then 0 else 0) else (if i.val < 587 then 0 else 0)) else (if i.val < 590 then (if i.val < 589 then 0 else 0) else (if i.val < 591 then 0 else 0)))) else (if i.val < 600 then (if i.val < 596 then (if i.val < 594 then (if i.val < 593 then 0 else 0) else (if i.val < 595 then 0 else 0)) else (if i.val < 598 then (if i.val < 597 then 0 else 0) else (if i.val < 599 then 0 else 0))) else (if i.val < 604 then (if i.val < 602 then (if i.val < 601 then 0 else 0) else (if i.val < 603 then 0 else 0)) else (if i.val < 606 then (if i.val < 605 then 0 else 0) else (if i.val < 607 then 0 else 0))))) else (if i.val < 624 then (if i.val < 616 then (if i.val < 612 then (if i.val < 610 then (if i.val < 609 then 0 else 0) else (if i.val < 611 then 0 else 0)) else (if i.val < 614 then (if i.val < 613 then 0 else 0) else (if i.val < 615 then 0 else 0))) else (if i.val < 620 then (if i.val < 618 then (if i.val < 617 then 0 else 0) else (if i.val < 619 then 0 else 0)) else (if i.val < 622 then (if i.val < 621 then 0 else 0) else (if i.val < 623 then 0 else 0)))) else (if i.val < 632 then (if i.val < 628 then (if i.val < 626 then (if i.val < 625 then 0 else 0) else (if i.val < 627 then 0 else 0)) else (if i.val < 630 then (if i.val < 629 then 0 else 0) else (if i.val < 631 then 0 else 0))) else (if i.val < 636 then (if i.val < 634 then (if i.val < 633 then 0 else 0) else (if i.val < 635 then 0 else 0)) else (if i.val < 638 then (if i.val < 637 then 0 else 0) else (if i.val < 639 then 0 else 0))))))) else (if i.val < 704 then (if i.val < 672 then (if i.val < 656 then (if i.val < 648 then (if i.val < 644 then (if i.val < 642 then (if i.val < 641 then 0 else 0) else (if i.val < 643 then 0 else 0)) else (if i.val < 646 then (if i.val < 645 then 0 else 0) else (if i.val < 647 then 0 else 0))) else (if i.val < 652 then (if i.val < 650 then (if i.val < 649 then 0 else 0) else (if i.val < 651 then 0 else 0)) else (if i.val < 654 then (if i.val < 653 then 0 else 0) else (if i.val < 655 then 0 else 0)))) else (if i.val < 664 then (if i.val < 660 then (if i.val < 658 then (if i.val < 657 then 0 else 0) else (if i.val < 659 then 0 else 0)) else (if i.val < 662 then (if i.val < 661 then 0 else 0) else (if i.val < 663 then 0 else 0))) else (if i.val < 668 then (if i.val < 666 then (if i.val < 665 then 0 else 0) else (if i.val < 667 then 0 else 0)) else (if i.val < 670 then (if i.val < 669 then 0 else 0) else (if i.val < 671 then 0 else 0))))) else (if i.val < 688 then (if i.val < 680 then (if i.val < 676 then (if i.val < 674 then (if i.val < 673 then 0 else 0) else (if i.val < 675 then 0 else 0)) else (if i.val < 678 then (if i.val < 677 then 0 else 0) else (if i.val < 679 then 0 else 0))) else (if i.val < 684 then (if i.val < 682 then (if i.val < 681 then 0 else 0) else (if i.val < 683 then 0 else 0)) else (if i.val < 686 then (if i.val < 685 then 0 else 0) else (if i.val < 687 then 0 else 0)))) else (if i.val < 696 then (if i.val < 692 then (if i.val < 690 then (if i.val < 689 then 0 else 0) else (if i.val < 691 then 0 else 0)) else (if i.val < 694 then (if i.val < 693 then 0 else 0) else (if i.val < 695 then 0 else 0))) else (if i.val < 700 then (if i.val < 698 then (if i.val < 697 then 0 else 0) else (if i.val < 699 then 0 else 0)) else (if i.val < 702 then (if i.val < 701 then 0 else 0) else (if i.val < 703 then 0 else 0)))))) else (if i.val < 736 then (if i.val < 720 then (if i.val < 712 then (if i.val < 708 then (if i.val < 706 then (if i.val < 705 then 0 else 0) else (if i.val < 707 then 0 else 0)) else (if i.val < 710 then (if i.val < 709 then 0 else 0) else (if i.val < 711 then 0 else 0))) else (if i.val < 716 then (if i.val < 714 then (if i.val < 713 then 0 else 0) else (if i.val < 715 then 0 else 0)) else (if i.val < 718 then (if i.val < 717 then 0 else 0) else (if i.val < 719 then 0 else 0)))) else (if i.val < 728 then (if i.val < 724 then (if i.val < 722 then (if i.val < 721 then 0 else 0) else (if i.val < 723 then 0 else 0)) else (if i.val < 726 then (if i.val < 725 then 0 else 0) else (if i.val < 727 then 0 else 0))) else (if i.val < 732 then (if i.val < 730 then (if i.val < 729 then 0 else 0) else (if i.val < 731 then 0 else 0)) else (if i.val < 734 then (if i.val < 733 then 0 else 0) else (if i.val < 735 then 0 else 0))))) else (if i.val < 752 then (if i.val < 744 then (if i.val < 740 then (if i.val < 738 then (if i.val < 737 then 0 else 0) else (if i.val < 739 then 0 else 0)) else (if i.val < 742 then (if i.val < 741 then 0 else 0) else (if i.val < 743 then 0 else 0))) else (if i.val < 748 then (if i.val < 746 then (if i.val < 745 then 0 else 0) else (if i.val < 747 then 0 else 0)) else (if i.val < 750 then (if i.val < 749 then 0 else 0) else (if i.val < 751 then 0 else 0)))) else (if i.val < 760 then (if i.val < 756 then (if i.val < 754 then (if i.val < 753 then 0 else 0) else (if i.val < 755 then 0 else 0)) else (if i.val < 758 then (if i.val < 757 then 0 else 0) else (if i.val < 759 then 0 else 0))) else (if i.val < 764 then (if i.val < 762 then (if i.val < 761 then 0 else 0) else (if i.val < 763 then 0 else 0)) else (if i.val < 766 then (if i.val < 765 then 0 else 0) else (if i.val < 767 then 0 else 0)))))))) else (if i.val < 896 then (if i.val < 832 then (if i.val < 800 then (if i.val < 784 then (if i.val < 776 then (if i.val < 772 then (if i.val < 770 then (if i.val < 769 then 0 else 0) else (if i.val < 771 then 0 else 0)) else (if i.val < 774 then (if i.val < 773 then 0 else 0) else (if i.val < 775 then 0 else 0))) else (if i.val < 780 then (if i.val < 778 then (if i.val < 777 then 0 else 0) else (if i.val < 779 then 0 else 0)) else (if i.val < 782 then (if i.val < 781 then 0 else 0) else (if i.val < 783 then 0 else 0)))) else (if i.val < 792 then (if i.val < 788 then (if i.val < 786 then (if i.val < 785 then 0 else 0) else (if i.val < 787 then 0 else 0)) else (if i.val < 790 then (if i.val < 789 then 0 else 0) else (if i.val < 791 then 0 else 0))) else (if i.val < 796 then (if i.val < 794 then (if i.val < 793 then 0 else 0) else (if i.val < 795 then 0 else 0)) else (if i.val < 798 then (if i.val < 797 then 0 else 0) else (if i.val < 799 then 0 else 0))))) else (if i.val < 816 then (if i.val < 808 then (if i.val < 804 then (if i.val < 802 then (if i.val < 801 then 0 else 0) else (if i.val < 803 then 0 else 0)) else (if i.val < 806 then (if i.val < 805 then 0 else 0) else (if i.val < 807 then 0 else 0))) else (if i.val < 812 then (if i.val < 810 then (if i.val < 809 then 0 else 0) else (if i.val < 811 then 0 else 0)) else (if i.val < 814 then (if i.val < 813 then 0 else 0) else (if i.val < 815 then 0 else 0)))) else (if i.val < 824 then (if i.val < 820 then (if i.val < 818 then (if i.val < 817 then 0 else 0) else (if i.val < 819 then 0 else 0)) else (if i.val < 822 then (if i.val < 821 then 0 else 0) else (if i.val < 823 then 0 else 0))) else (if i.val < 828 then (if i.val < 826 then (if i.val < 825 then 0 else 0) else (if i.val < 827 then 0 else 0)) else (if i.val < 830 then (if i.val < 829 then 0 else 0) else (if i.val < 831 then 0 else 0)))))) else (if i.val < 864 then (if i.val < 848 then (if i.val < 840 then (if i.val < 836 then (if i.val < 834 then (if i.val < 833 then 0 else 0) else (if i.val < 835 then 0 else 0)) else (if i.val < 838 then (if i.val < 837 then 0 else 0) else (if i.val < 839 then 0 else 0))) else (if i.val < 844 then (if i.val < 842 then (if i.val < 841 then 0 else 0) else (if i.val < 843 then 0 else 0)) else (if i.val < 846 then (if i.val < 845 then 0 else 0) else (if i.val < 847 then 0 else 0)))) else (if i.val < 856 then (if i.val < 852 then (if i.val < 850 then (if i.val < 849 then 0 else 0) else (if i.val < 851 then 0 else 0)) else (if i.val < 854 then (if i.val < 853 then 0 else 0) else (if i.val < 855 then 0 else 0))) else (if i.val < 860 then (if i.val < 858 then (if i.val < 857 then 0 else 0) else (if i.val < 859 then 0 else 0)) else (if i.val < 862 then (if i.val < 861 then 0 else 0) else (if i.val < 863 then 0 else 0))))) else (if i.val < 880 then (if i.val < 872 then (if i.val < 868 then (if i.val < 866 then (if i.val < 865 then 0 else 0) else (if i.val < 867 then 0 else 0)) else (if i.val < 870 then (if i.val < 869 then 0 else 0) else (if i.val < 871 then 0 else 0))) else (if i.val < 876 then (if i.val < 874 then (if i.val < 873 then 0 else 0) else (if i.val < 875 then 0 else 0)) else (if i.val < 878 then (if i.val < 877 then 0 else 0) else (if i.val < 879 then 0 else 0)))) else (if i.val < 888 then (if i.val < 884 then (if i.val < 882 then (if i.val < 881 then 0 else 0) else (if i.val < 883 then 0 else 0)) else (if i.val < 886 then (if i.val < 885 then 0 else 0) else (if i.val < 887 then 0 else 0))) else (if i.val < 892 then (if i.val < 890 then (if i.val < 889 then 0 else 0) else (if i.val < 891 then 0 else 0)) else (if i.val < 894 then (if i.val < 893 then 0 else 0) else (if i.val < 895 then 0 else 0))))))) else (if i.val < 960 then (if i.val < 928 then (if i.val < 912 then (if i.val < 904 then (if i.val < 900 then (if i.val < 898 then (if i.val < 897 then 0 else 0) else (if i.val < 899 then 0 else 0)) else (if i.val < 902 then (if i.val < 901 then 0 else 0) else (if i.val < 903 then 0 else 0))) else (if i.val < 908 then (if i.val < 906 then (if i.val < 905 then 0 else 0) else (if i.val < 907 then 0 else 0)) else (if i.val < 910 then (if i.val < 909 then 0 else 0) else (if i.val < 911 then 0 else 0)))) else (if i.val < 920 then (if i.val < 916 then (if i.val < 914 then (if i.val < 913 then 0 else 0) else (if i.val < 915 then 0 else 0)) else (if i.val < 918 then (if i.val < 917 then 0 else 0) else (if i.val < 919 then 0 else 0))) else (if i.val < 924 then (if i.val < 922 then (if i.val < 921 then 0 else 0) else (if i.val < 923 then 0 else 0)) else (if i.val < 926 then (if i.val < 925 then 0 else 0) else (if i.val < 927 then 0 else 0))))) else (if i.val < 944 then (if i.val < 936 then (if i.val < 932 then (if i.val < 930 then (if i.val < 929 then 0 else 0) else (if i.val < 931 then 0 else 0)) else (if i.val < 934 then (if i.val < 933 then 0 else 0) else (if i.val < 935 then 0 else 0))) else (if i.val < 940 then (if i.val < 938 then (if i.val < 937 then 0 else 0) else (if i.val < 939 then 0 else 0)) else (if i.val < 942 then (if i.val < 941 then 0 else 0) else (if i.val < 943 then 0 else 0)))) else (if i.val < 952 then (if i.val < 948 then (if i.val < 946 then (if i.val < 945 then 0 else 0) else (if i.val < 947 then 0 else 0)) else (if i.val < 950 then (if i.val < 949 then 0 else 0) else (if i.val < 951 then 0 else 0))) else (if i.val < 956 then (if i.val < 954 then (if i.val < 953 then 0 else 0) else (if i.val < 955 then 0 else 0)) else (if i.val < 958 then (if i.val < 957 then 0 else 0) else (if i.val < 959 then 0 else 0)))))) else (if i.val < 992 then (if i.val < 976 then (if i.val < 968 then (if i.val < 964 then (if i.val < 962 then (if i.val < 961 then 0 else 0) else (if i.val < 963 then 0 else 0)) else (if i.val < 966 then (if i.val < 965 then 0 else 0) else (if i.val < 967 then 0 else 0))) else (if i.val < 972 then (if i.val < 970 then (if i.val < 969 then 0 else 0) else (if i.val < 971 then 0 else 0)) else (if i.val < 974 then (if i.val < 973 then 0 else 0) else (if i.val < 975 then 0 else 0)))) else (if i.val < 984 then (if i.val < 980 then (if i.val < 978 then (if i.val < 977 then 0 else 0) else (if i.val < 979 then 0 else 0)) else (if i.val < 982 then (if i.val < 981 then 0 else 0) else (if i.val < 983 then 0 else 0))) else (if i.val < 988 then (if i.val < 986 then (if i.val < 985 then 0 else 0) else (if i.val < 987 then 0 else 0)) else (if i.val < 990 then (if i.val < 989 then 0 else 0) else (if i.val < 991 then 0 else 0))))) else (if i.val < 1008 then (if i.val < 1000 then (if i.val < 996 then (if i.val < 994 then (if i.val < 993 then 0 else 0) else (if i.val < 995 then 0 else 0)) else (if i.val < 998 then (if i.val < 997 then 0 else 0) else (if i.val < 999 then 0 else 0))) else (if i.val < 1004 then (if i.val < 1002 then (if i.val < 1001 then 0 else 0) else (if i.val < 1003 then 0 else 0)) else (if i.val < 1006 then (if i.val < 1005 then 0 else 0) else (if i.val < 1007 then 0 else 0)))) else (if i.val < 1016 then (if i.val < 1012 then (if i.val < 1010 then (if i.val < 1009 then 0 else 0) else (if i.val < 1011 then 0 else 0)) else (if i.val < 1014 then (if i.val < 1013 then 0 else 0) else (if i.val < 1015 then 0 else 0))) else (if i.val < 1020 then (if i.val < 1018 then (if i.val < 1017 then 0 else 0) else (if i.val < 1019 then 0 else 0)) else (if i.val < 1022 then (if i.val < 1021 then 0 else 0) else (if i.val < 1023 then 0 else 0)))))))))))
    (fun j => (if j.val < 2 then (if j.val < 1 then 0 else 90) else (if j.val < 3 then 67 else 12)))
    (Fin.addCases (m := 512) (n := 512) (Fin.addCases (m := 256) (n := 256) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)))) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))))) (Fin.addCases (m := 256) (n := 256) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)))) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)))))) (by decide +kernel)

theorem beta_range : betaCertificate.hom.range =
    Subgroup.closure (Set.range quotientGenerators) :=
  betaCertificate.hom_range_eq_of_rows quotientCertificate
    (fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 2 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 5) else (if i.val < 7 then 6 else 7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 8 else 9) else (if i.val < 11 then 10 else 11)) else (if i.val < 14 then (if i.val < 13 then 12 else 13) else (if i.val < 15 then 14 else 15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 16 else 17) else (if i.val < 19 then 18 else 19)) else (if i.val < 22 then (if i.val < 21 then 20 else 21) else (if i.val < 23 then 22 else 23))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 24 else 25) else (if i.val < 27 then 26 else 27)) else (if i.val < 30 then (if i.val < 29 then 28 else 29) else (if i.val < 31 then 30 else 31))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 32 else 33) else (if i.val < 35 then 34 else 35)) else (if i.val < 38 then (if i.val < 37 then 36 else 37) else (if i.val < 39 then 38 else 39))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 40 else 41) else (if i.val < 43 then 42 else 43)) else (if i.val < 46 then (if i.val < 45 then 44 else 45) else (if i.val < 47 then 46 else 47)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 48 else 49) else (if i.val < 51 then 50 else 51)) else (if i.val < 54 then (if i.val < 53 then 52 else 53) else (if i.val < 55 then 54 else 55))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 56 else 57) else (if i.val < 59 then 58 else 59)) else (if i.val < 62 then (if i.val < 61 then 60 else 61) else (if i.val < 63 then 62 else 63)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 64 else 65) else (if i.val < 67 then 66 else 67)) else (if i.val < 70 then (if i.val < 69 then 68 else 69) else (if i.val < 71 then 70 else 71))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 72 else 73) else (if i.val < 75 then 74 else 75)) else (if i.val < 78 then (if i.val < 77 then 76 else 77) else (if i.val < 79 then 78 else 79)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 80 else 81) else (if i.val < 83 then 82 else 83)) else (if i.val < 86 then (if i.val < 85 then 84 else 85) else (if i.val < 87 then 86 else 87))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 88 else 89) else (if i.val < 91 then 90 else 91)) else (if i.val < 94 then (if i.val < 93 then 92 else 93) else (if i.val < 95 then 94 else 95))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 96 else 97) else (if i.val < 99 then 98 else 99)) else (if i.val < 102 then (if i.val < 101 then 100 else 101) else (if i.val < 103 then 102 else 103))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 104 else 105) else (if i.val < 107 then 106 else 107)) else (if i.val < 110 then (if i.val < 109 then 108 else 109) else (if i.val < 111 then 110 else 111)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 112 else 113) else (if i.val < 115 then 114 else 115)) else (if i.val < 118 then (if i.val < 117 then 116 else 117) else (if i.val < 119 then 118 else 119))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 120 else 121) else (if i.val < 123 then 122 else 123)) else (if i.val < 126 then (if i.val < 125 then 124 else 125) else (if i.val < 127 then 126 else 127))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 128 else 129) else (if i.val < 131 then 130 else 131)) else (if i.val < 134 then (if i.val < 133 then 132 else 133) else (if i.val < 135 then 134 else 135))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 136 else 137) else (if i.val < 139 then 138 else 139)) else (if i.val < 142 then (if i.val < 141 then 140 else 141) else (if i.val < 143 then 142 else 143)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 144 else 145) else (if i.val < 147 then 146 else 147)) else (if i.val < 150 then (if i.val < 149 then 148 else 149) else (if i.val < 151 then 150 else 151))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 152 else 153) else (if i.val < 155 then 154 else 155)) else (if i.val < 158 then (if i.val < 157 then 156 else 157) else (if i.val < 159 then 158 else 159))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 160 else 161) else (if i.val < 163 then 162 else 163)) else (if i.val < 166 then (if i.val < 165 then 164 else 165) else (if i.val < 167 then 166 else 167))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 168 else 169) else (if i.val < 171 then 170 else 171)) else (if i.val < 174 then (if i.val < 173 then 172 else 173) else (if i.val < 175 then 174 else 175)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 176 else 177) else (if i.val < 179 then 178 else 179)) else (if i.val < 182 then (if i.val < 181 then 180 else 181) else (if i.val < 183 then 182 else 183))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 184 else 185) else (if i.val < 187 then 186 else 187)) else (if i.val < 190 then (if i.val < 189 then 188 else 189) else (if i.val < 191 then 190 else 191)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 192 else 193) else (if i.val < 195 then 194 else 195)) else (if i.val < 198 then (if i.val < 197 then 196 else 197) else (if i.val < 199 then 198 else 199))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 200 else 201) else (if i.val < 203 then 202 else 203)) else (if i.val < 206 then (if i.val < 205 then 204 else 205) else (if i.val < 207 then 206 else 207)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 208 else 209) else (if i.val < 211 then 210 else 211)) else (if i.val < 214 then (if i.val < 213 then 212 else 213) else (if i.val < 215 then 214 else 215))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 216 else 217) else (if i.val < 219 then 218 else 219)) else (if i.val < 222 then (if i.val < 221 then 220 else 221) else (if i.val < 223 then 222 else 223))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 224 else 225) else (if i.val < 227 then 226 else 227)) else (if i.val < 230 then (if i.val < 229 then 228 else 229) else (if i.val < 231 then 230 else 231))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 232 else 233) else (if i.val < 235 then 234 else 235)) else (if i.val < 238 then (if i.val < 237 then 236 else 237) else (if i.val < 239 then 238 else 239)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 240 else 241) else (if i.val < 243 then 242 else 243)) else (if i.val < 246 then (if i.val < 245 then 244 else 245) else (if i.val < 247 then 246 else 247))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 248 else 249) else (if i.val < 251 then 250 else 251)) else (if i.val < 254 then (if i.val < 253 then 252 else 253) else (if i.val < 255 then 254 else 255)))))))))
    (fun j => (if j.val < 128 then (if j.val < 64 then (if j.val < 32 then (if j.val < 16 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 1) else (if j.val < 3 then 2 else 3)) else (if j.val < 6 then (if j.val < 5 then 4 else 5) else (if j.val < 7 then 6 else 7))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 8 else 9) else (if j.val < 11 then 10 else 11)) else (if j.val < 14 then (if j.val < 13 then 12 else 13) else (if j.val < 15 then 14 else 15)))) else (if j.val < 24 then (if j.val < 20 then (if j.val < 18 then (if j.val < 17 then 16 else 17) else (if j.val < 19 then 18 else 19)) else (if j.val < 22 then (if j.val < 21 then 20 else 21) else (if j.val < 23 then 22 else 23))) else (if j.val < 28 then (if j.val < 26 then (if j.val < 25 then 24 else 25) else (if j.val < 27 then 26 else 27)) else (if j.val < 30 then (if j.val < 29 then 28 else 29) else (if j.val < 31 then 30 else 31))))) else (if j.val < 48 then (if j.val < 40 then (if j.val < 36 then (if j.val < 34 then (if j.val < 33 then 32 else 33) else (if j.val < 35 then 34 else 35)) else (if j.val < 38 then (if j.val < 37 then 36 else 37) else (if j.val < 39 then 38 else 39))) else (if j.val < 44 then (if j.val < 42 then (if j.val < 41 then 40 else 41) else (if j.val < 43 then 42 else 43)) else (if j.val < 46 then (if j.val < 45 then 44 else 45) else (if j.val < 47 then 46 else 47)))) else (if j.val < 56 then (if j.val < 52 then (if j.val < 50 then (if j.val < 49 then 48 else 49) else (if j.val < 51 then 50 else 51)) else (if j.val < 54 then (if j.val < 53 then 52 else 53) else (if j.val < 55 then 54 else 55))) else (if j.val < 60 then (if j.val < 58 then (if j.val < 57 then 56 else 57) else (if j.val < 59 then 58 else 59)) else (if j.val < 62 then (if j.val < 61 then 60 else 61) else (if j.val < 63 then 62 else 63)))))) else (if j.val < 96 then (if j.val < 80 then (if j.val < 72 then (if j.val < 68 then (if j.val < 66 then (if j.val < 65 then 64 else 65) else (if j.val < 67 then 66 else 67)) else (if j.val < 70 then (if j.val < 69 then 68 else 69) else (if j.val < 71 then 70 else 71))) else (if j.val < 76 then (if j.val < 74 then (if j.val < 73 then 72 else 73) else (if j.val < 75 then 74 else 75)) else (if j.val < 78 then (if j.val < 77 then 76 else 77) else (if j.val < 79 then 78 else 79)))) else (if j.val < 88 then (if j.val < 84 then (if j.val < 82 then (if j.val < 81 then 80 else 81) else (if j.val < 83 then 82 else 83)) else (if j.val < 86 then (if j.val < 85 then 84 else 85) else (if j.val < 87 then 86 else 87))) else (if j.val < 92 then (if j.val < 90 then (if j.val < 89 then 88 else 89) else (if j.val < 91 then 90 else 91)) else (if j.val < 94 then (if j.val < 93 then 92 else 93) else (if j.val < 95 then 94 else 95))))) else (if j.val < 112 then (if j.val < 104 then (if j.val < 100 then (if j.val < 98 then (if j.val < 97 then 96 else 97) else (if j.val < 99 then 98 else 99)) else (if j.val < 102 then (if j.val < 101 then 100 else 101) else (if j.val < 103 then 102 else 103))) else (if j.val < 108 then (if j.val < 106 then (if j.val < 105 then 104 else 105) else (if j.val < 107 then 106 else 107)) else (if j.val < 110 then (if j.val < 109 then 108 else 109) else (if j.val < 111 then 110 else 111)))) else (if j.val < 120 then (if j.val < 116 then (if j.val < 114 then (if j.val < 113 then 112 else 113) else (if j.val < 115 then 114 else 115)) else (if j.val < 118 then (if j.val < 117 then 116 else 117) else (if j.val < 119 then 118 else 119))) else (if j.val < 124 then (if j.val < 122 then (if j.val < 121 then 120 else 121) else (if j.val < 123 then 122 else 123)) else (if j.val < 126 then (if j.val < 125 then 124 else 125) else (if j.val < 127 then 126 else 127))))))) else (if j.val < 192 then (if j.val < 160 then (if j.val < 144 then (if j.val < 136 then (if j.val < 132 then (if j.val < 130 then (if j.val < 129 then 128 else 129) else (if j.val < 131 then 130 else 131)) else (if j.val < 134 then (if j.val < 133 then 132 else 133) else (if j.val < 135 then 134 else 135))) else (if j.val < 140 then (if j.val < 138 then (if j.val < 137 then 136 else 137) else (if j.val < 139 then 138 else 139)) else (if j.val < 142 then (if j.val < 141 then 140 else 141) else (if j.val < 143 then 142 else 143)))) else (if j.val < 152 then (if j.val < 148 then (if j.val < 146 then (if j.val < 145 then 144 else 145) else (if j.val < 147 then 146 else 147)) else (if j.val < 150 then (if j.val < 149 then 148 else 149) else (if j.val < 151 then 150 else 151))) else (if j.val < 156 then (if j.val < 154 then (if j.val < 153 then 152 else 153) else (if j.val < 155 then 154 else 155)) else (if j.val < 158 then (if j.val < 157 then 156 else 157) else (if j.val < 159 then 158 else 159))))) else (if j.val < 176 then (if j.val < 168 then (if j.val < 164 then (if j.val < 162 then (if j.val < 161 then 160 else 161) else (if j.val < 163 then 162 else 163)) else (if j.val < 166 then (if j.val < 165 then 164 else 165) else (if j.val < 167 then 166 else 167))) else (if j.val < 172 then (if j.val < 170 then (if j.val < 169 then 168 else 169) else (if j.val < 171 then 170 else 171)) else (if j.val < 174 then (if j.val < 173 then 172 else 173) else (if j.val < 175 then 174 else 175)))) else (if j.val < 184 then (if j.val < 180 then (if j.val < 178 then (if j.val < 177 then 176 else 177) else (if j.val < 179 then 178 else 179)) else (if j.val < 182 then (if j.val < 181 then 180 else 181) else (if j.val < 183 then 182 else 183))) else (if j.val < 188 then (if j.val < 186 then (if j.val < 185 then 184 else 185) else (if j.val < 187 then 186 else 187)) else (if j.val < 190 then (if j.val < 189 then 188 else 189) else (if j.val < 191 then 190 else 191)))))) else (if j.val < 224 then (if j.val < 208 then (if j.val < 200 then (if j.val < 196 then (if j.val < 194 then (if j.val < 193 then 192 else 193) else (if j.val < 195 then 194 else 195)) else (if j.val < 198 then (if j.val < 197 then 196 else 197) else (if j.val < 199 then 198 else 199))) else (if j.val < 204 then (if j.val < 202 then (if j.val < 201 then 200 else 201) else (if j.val < 203 then 202 else 203)) else (if j.val < 206 then (if j.val < 205 then 204 else 205) else (if j.val < 207 then 206 else 207)))) else (if j.val < 216 then (if j.val < 212 then (if j.val < 210 then (if j.val < 209 then 208 else 209) else (if j.val < 211 then 210 else 211)) else (if j.val < 214 then (if j.val < 213 then 212 else 213) else (if j.val < 215 then 214 else 215))) else (if j.val < 220 then (if j.val < 218 then (if j.val < 217 then 216 else 217) else (if j.val < 219 then 218 else 219)) else (if j.val < 222 then (if j.val < 221 then 220 else 221) else (if j.val < 223 then 222 else 223))))) else (if j.val < 240 then (if j.val < 232 then (if j.val < 228 then (if j.val < 226 then (if j.val < 225 then 224 else 225) else (if j.val < 227 then 226 else 227)) else (if j.val < 230 then (if j.val < 229 then 228 else 229) else (if j.val < 231 then 230 else 231))) else (if j.val < 236 then (if j.val < 234 then (if j.val < 233 then 232 else 233) else (if j.val < 235 then 234 else 235)) else (if j.val < 238 then (if j.val < 237 then 236 else 237) else (if j.val < 239 then 238 else 239)))) else (if j.val < 248 then (if j.val < 244 then (if j.val < 242 then (if j.val < 241 then 240 else 241) else (if j.val < 243 then 242 else 243)) else (if j.val < 246 then (if j.val < 245 then 244 else 245) else (if j.val < 247 then 246 else 247))) else (if j.val < 252 then (if j.val < 250 then (if j.val < 249 then 248 else 249) else (if j.val < 251 then 250 else 251)) else (if j.val < 254 then (if j.val < 253 then 252 else 253) else (if j.val < 255 then 254 else 255)))))))))
    (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)))) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))))

theorem beta_kernel : betaCertificate.hom.ker.map
    (Subgroup.closure (Set.range betaGenerators)).subtype =
      Subgroup.closure (Set.range coverKernelGenerators) :=
  betaCertificate.kernel_image_eq_of_rows coverKernelCertificate
    (fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 0 else 0) else (if i.val < 7 then 0 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 0) else (if i.val < 11 then 0 else 0)) else (if i.val < 14 then (if i.val < 13 then 0 else 0) else (if i.val < 15 then 0 else 0)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 0) else (if i.val < 19 then 0 else 0)) else (if i.val < 22 then (if i.val < 21 then 0 else 0) else (if i.val < 23 then 0 else 0))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 0 else 0) else (if i.val < 27 then 0 else 0)) else (if i.val < 30 then (if i.val < 29 then 0 else 0) else (if i.val < 31 then 0 else 0))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 0 else 0) else (if i.val < 35 then 0 else 0)) else (if i.val < 38 then (if i.val < 37 then 0 else 0) else (if i.val < 39 then 0 else 0))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 0 else 0) else (if i.val < 43 then 0 else 0)) else (if i.val < 46 then (if i.val < 45 then 0 else 0) else (if i.val < 47 then 0 else 0)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 0 else 0) else (if i.val < 51 then 0 else 0)) else (if i.val < 54 then (if i.val < 53 then 0 else 0) else (if i.val < 55 then 0 else 0))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 0 else 0) else (if i.val < 59 then 0 else 0)) else (if i.val < 62 then (if i.val < 61 then 0 else 0) else (if i.val < 63 then 0 else 0)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 0 else 0) else (if i.val < 67 then 0 else 0)) else (if i.val < 70 then (if i.val < 69 then 0 else 0) else (if i.val < 71 then 0 else 0))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 0 else 0) else (if i.val < 75 then 0 else 0)) else (if i.val < 78 then (if i.val < 77 then 0 else 0) else (if i.val < 79 then 0 else 0)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 0 else 0) else (if i.val < 83 then 0 else 0)) else (if i.val < 86 then (if i.val < 85 then 0 else 0) else (if i.val < 87 then 0 else 0))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 0 else 0) else (if i.val < 91 then 0 else 0)) else (if i.val < 94 then (if i.val < 93 then 0 else 0) else (if i.val < 95 then 0 else 0))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 0 else 0) else (if i.val < 99 then 0 else 0)) else (if i.val < 102 then (if i.val < 101 then 0 else 0) else (if i.val < 103 then 0 else 0))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 0 else 0) else (if i.val < 107 then 0 else 0)) else (if i.val < 110 then (if i.val < 109 then 0 else 0) else (if i.val < 111 then 0 else 0)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 0 else 0) else (if i.val < 115 then 0 else 0)) else (if i.val < 118 then (if i.val < 117 then 0 else 0) else (if i.val < 119 then 0 else 0))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 0 else 0) else (if i.val < 123 then 0 else 0)) else (if i.val < 126 then (if i.val < 125 then 0 else 0) else (if i.val < 127 then 0 else 0))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 0 else 0) else (if i.val < 131 then 0 else 0)) else (if i.val < 134 then (if i.val < 133 then 0 else 0) else (if i.val < 135 then 0 else 0))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 0 else 0) else (if i.val < 139 then 0 else 0)) else (if i.val < 142 then (if i.val < 141 then 0 else 0) else (if i.val < 143 then 0 else 0)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 0 else 0) else (if i.val < 147 then 0 else 0)) else (if i.val < 150 then (if i.val < 149 then 0 else 0) else (if i.val < 151 then 0 else 0))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 0 else 0) else (if i.val < 155 then 0 else 0)) else (if i.val < 158 then (if i.val < 157 then 0 else 0) else (if i.val < 159 then 0 else 0))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 0 else 0) else (if i.val < 163 then 0 else 0)) else (if i.val < 166 then (if i.val < 165 then 0 else 0) else (if i.val < 167 then 0 else 0))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 0 else 0) else (if i.val < 171 then 0 else 0)) else (if i.val < 174 then (if i.val < 173 then 0 else 0) else (if i.val < 175 then 0 else 0)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 0 else 0) else (if i.val < 179 then 0 else 0)) else (if i.val < 182 then (if i.val < 181 then 0 else 0) else (if i.val < 183 then 0 else 0))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 0 else 0) else (if i.val < 187 then 0 else 0)) else (if i.val < 190 then (if i.val < 189 then 0 else 0) else (if i.val < 191 then 0 else 0)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 0 else 0) else (if i.val < 195 then 0 else 0)) else (if i.val < 198 then (if i.val < 197 then 0 else 0) else (if i.val < 199 then 0 else 0))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 0 else 0) else (if i.val < 203 then 0 else 0)) else (if i.val < 206 then (if i.val < 205 then 0 else 0) else (if i.val < 207 then 0 else 0)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 0 else 0) else (if i.val < 211 then 0 else 0)) else (if i.val < 214 then (if i.val < 213 then 0 else 0) else (if i.val < 215 then 0 else 0))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 0 else 0) else (if i.val < 219 then 0 else 0)) else (if i.val < 222 then (if i.val < 221 then 0 else 0) else (if i.val < 223 then 0 else 0))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 0 else 0) else (if i.val < 227 then 0 else 0)) else (if i.val < 230 then (if i.val < 229 then 0 else 0) else (if i.val < 231 then 0 else 0))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 0 else 0) else (if i.val < 235 then 0 else 0)) else (if i.val < 238 then (if i.val < 237 then 0 else 0) else (if i.val < 239 then 0 else 0)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 0 else 0) else (if i.val < 243 then 0 else 0)) else (if i.val < 246 then (if i.val < 245 then 0 else 0) else (if i.val < 247 then 0 else 0))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 0 else 0) else (if i.val < 251 then 0 else 0)) else (if i.val < 254 then (if i.val < 253 then 0 else 0) else (if i.val < 255 then 0 else 0)))))))))
    (fun j => 0)
    (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 32) (n := 32) (by decide +kernel) (by decide +kernel)))) (by decide +kernel)

end SymmetricSubgroupAsymptotics.BinaryChart16T1086
