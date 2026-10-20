import SymmetricSubgroupAsymptotics.FiniteGroupCertificates

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

def alphaSourceLiteral384 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral385 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral386 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral387 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,8,9,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral388 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral389 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral390 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,8,9,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral391 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral392 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral393 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral394 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral395 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral396 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral397 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral398 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral399 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral400 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral401 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral402 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral403 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral404 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral405 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral406 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral407 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral408 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral409 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral410 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral411 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral412 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral413 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral414 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral415 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral416 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral417 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral418 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral419 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral420 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral421 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral422 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral423 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral424 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral425 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral426 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral427 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral428 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral429 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral430 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral431 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral432 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral433 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral434 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral435 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral436 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral437 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral438 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral439 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral440 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral441 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral442 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral443 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral444 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral445 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral446 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral447 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
