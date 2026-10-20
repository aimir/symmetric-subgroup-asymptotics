import SymmetricSubgroupAsymptotics.FiniteGroupCertificates

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

def alphaSourceLiteral512 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral513 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral514 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral515 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral516 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,9,8,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral517 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral518 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral519 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral520 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral521 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral522 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral523 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral524 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral525 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral526 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral527 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral528 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral529 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral530 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral531 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral532 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral533 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral534 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral535 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral536 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral537 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral538 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral539 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral540 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral541 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral542 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral543 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral544 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral545 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral546 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral547 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral548 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral549 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,8,9,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral550 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral551 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral552 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral553 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral554 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral555 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral556 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral557 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral558 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral559 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral560 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral561 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral562 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral563 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral564 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral565 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral566 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral567 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral568 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral569 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral570 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,12,13,10,11,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral571 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral572 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral573 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral574 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral575 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
