import SymmetricSubgroupAsymptotics.FiniteGroupCertificates

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

def alphaSourceLiteral576 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral577 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral578 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral579 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral580 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral581 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral582 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral583 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,9,8,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral584 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral585 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral586 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,12,13,10,11,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral587 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral588 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral589 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral590 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral591 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral592 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral593 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral594 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral595 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral596 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral597 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral598 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral599 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral600 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral601 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral602 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral603 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral604 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral605 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral606 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral607 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral608 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral609 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral610 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral611 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral612 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,8,9,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral613 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral614 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral615 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral616 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,8,9,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral617 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral618 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral619 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,8,9,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral620 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral621 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral622 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral623 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral624 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral625 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral626 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral627 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral628 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral629 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral630 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral631 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral632 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral633 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral634 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral635 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral636 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral637 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral638 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral639 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
