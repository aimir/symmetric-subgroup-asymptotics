import SymmetricSubgroupAsymptotics.FiniteGroupCertificates

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

def alphaSourceLiteral640 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral641 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral642 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral643 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral644 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral645 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral646 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral647 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral648 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral649 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral650 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral651 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral652 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral653 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral654 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral655 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral656 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral657 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral658 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral659 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral660 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral661 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral662 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral663 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral664 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral665 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral666 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral667 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral668 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral669 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral670 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,10,11,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral671 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral672 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral673 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral674 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral675 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral676 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral677 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral678 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral679 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral680 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral681 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral682 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral683 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral684 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral685 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,8,9,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral686 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral687 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral688 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral689 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral690 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral691 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral692 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral693 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral694 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral695 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral696 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral697 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral698 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral699 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral700 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral701 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral702 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral703 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
