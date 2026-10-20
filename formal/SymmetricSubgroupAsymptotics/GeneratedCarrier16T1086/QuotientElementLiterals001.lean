import SymmetricSubgroupAsymptotics.FiniteGroupCertificates

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

def quotientElementLiteral64 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral65 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral66 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral67 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral68 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral69 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral70 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral71 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral72 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral73 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral74 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral75 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral76 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral77 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral78 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral79 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral80 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral81 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral82 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral83 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral84 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral85 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral86 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral87 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral88 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral89 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral90 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral91 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral92 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral93 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral94 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral95 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral96 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral97 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral98 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral99 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral100 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral101 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral102 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral103 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral104 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral105 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral106 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral107 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral108 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral109 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral110 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral111 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral112 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral113 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral114 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral115 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral116 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral117 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral118 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral119 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral120 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral121 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral122 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral123 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral124 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral125 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral126 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral127 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
