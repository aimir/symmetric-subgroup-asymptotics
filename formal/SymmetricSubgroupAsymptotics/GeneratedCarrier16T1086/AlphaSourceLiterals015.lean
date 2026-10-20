import SymmetricSubgroupAsymptotics.FiniteGroupCertificates

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

def alphaSourceLiteral960 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral961 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral962 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral963 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral964 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral965 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral966 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral967 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral968 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral969 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral970 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral971 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral972 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral973 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral974 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral975 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral976 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral977 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral978 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral979 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral980 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral981 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral982 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral983 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral984 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral985 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral986 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral987 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral988 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral989 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral990 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral991 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral992 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral993 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral994 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral995 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral996 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral997 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral998 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral999 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1000 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1001 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1002 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1003 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1004 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1005 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1006 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1007 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1008 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1009 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1010 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1011 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1012 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1013 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1014 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1015 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1016 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1017 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1018 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1019 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1020 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1021 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1022 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral1023 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
