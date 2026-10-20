import SymmetricSubgroupAsymptotics.FiniteGroupCertificates

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

def alphaSourceLiteral832 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral833 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral834 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral835 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral836 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral837 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral838 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral839 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral840 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral841 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral842 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral843 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral844 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral845 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral846 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral847 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral848 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral849 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral850 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral851 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral852 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral853 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral854 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral855 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral856 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral857 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral858 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral859 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral860 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral861 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral862 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral863 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral864 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral865 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral866 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral867 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral868 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral869 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,10,11,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral870 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral871 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral872 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral873 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral874 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,10,11,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral875 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral876 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral877 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral878 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral879 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral880 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral881 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,10,11,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral882 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral883 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral884 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral885 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral886 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral887 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral888 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral889 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral890 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,8,9,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral891 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral892 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral893 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,15,14,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,8,9,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral894 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,9,8,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral895 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
