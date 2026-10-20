import SymmetricSubgroupAsymptotics.FiniteGroupCertificates

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

def betaTargetLiteral64 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral65 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral66 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral67 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral68 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral69 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral70 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral71 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral72 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral73 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral74 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral75 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral76 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral77 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral78 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral79 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral80 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral81 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral82 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral83 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral84 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral85 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral86 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral87 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral88 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral89 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral90 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral91 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral92 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral93 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral94 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral95 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral96 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral97 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral98 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral99 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral100 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral101 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral102 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral103 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral104 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral105 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral106 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral107 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral108 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral109 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral110 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral111 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral112 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral113 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral114 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral115 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral116 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral117 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral118 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral119 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral120 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral121 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral122 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral123 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral124 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral125 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral126 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def betaTargetLiteral127 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
