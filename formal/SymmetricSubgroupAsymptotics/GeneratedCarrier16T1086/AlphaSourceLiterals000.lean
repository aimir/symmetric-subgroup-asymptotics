import SymmetricSubgroupAsymptotics.FiniteGroupCertificates

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

def alphaSourceLiteral0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral4 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral5 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral6 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral7 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral8 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral9 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral10 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral11 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral12 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral13 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral14 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral15 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral16 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral17 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral18 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral19 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral20 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral21 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral22 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral23 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral24 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral25 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral26 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral27 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral28 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral29 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral30 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral31 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral32 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral33 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral34 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral35 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral36 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral37 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral38 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral39 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral40 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral41 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral42 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,15,14,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral43 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral44 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,9,8,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral45 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,10,11,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,8,9,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral46 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral47 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral48 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,12,13,10,11,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral49 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral50 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral51 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral52 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral53 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral54 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral55 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral56 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral57 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral58 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral59 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral60 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral61 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral62 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral63 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
