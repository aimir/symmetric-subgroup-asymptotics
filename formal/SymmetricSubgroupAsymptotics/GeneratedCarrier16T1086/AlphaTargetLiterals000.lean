import SymmetricSubgroupAsymptotics.FiniteGroupCertificates

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

def alphaTargetLiteral0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral3 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral4 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral5 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral6 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral7 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral8 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral9 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral10 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral11 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral12 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral13 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral14 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral15 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral16 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral17 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral18 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral19 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral20 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral21 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral22 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral23 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral24 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral25 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral26 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral27 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral28 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral29 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral30 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral31 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral32 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral33 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral34 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral35 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral36 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral37 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral38 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral39 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral40 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral41 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral42 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral43 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral44 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral45 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral46 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral47 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral48 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral49 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral50 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral51 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral52 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral53 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral54 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral55 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral56 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral57 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral58 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral59 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral60 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral61 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral62 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral63 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
