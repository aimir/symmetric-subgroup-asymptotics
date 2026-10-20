import SymmetricSubgroupAsymptotics.FiniteGroupCertificates

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

def quotientElementLiteral0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral3 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral4 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral5 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral6 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral7 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral8 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral9 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral10 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral11 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral12 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral13 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral14 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral15 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral16 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral17 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral18 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral19 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral20 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral21 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral22 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral23 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral24 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral25 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral26 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral27 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral28 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral29 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral30 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral31 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral32 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral33 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral34 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral35 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral36 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral37 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral38 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral39 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral40 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral41 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral42 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral43 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral44 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral45 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral46 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral47 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral48 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral49 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral50 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral51 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral52 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral53 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral54 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral55 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral56 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral57 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral58 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral59 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral60 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral61 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral62 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral63 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
