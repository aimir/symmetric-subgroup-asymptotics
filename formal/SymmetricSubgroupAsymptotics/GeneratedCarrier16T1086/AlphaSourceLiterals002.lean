import SymmetricSubgroupAsymptotics.FiniteGroupCertificates

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

def alphaSourceLiteral128 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral129 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,10,11,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral130 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,8,9,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral131 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral132 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral133 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,12,13,10,11,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral134 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral135 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral136 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,12,13,10,11,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral137 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral138 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral139 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral140 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral141 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral142 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral143 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral144 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral145 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral146 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral147 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral148 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral149 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,15,14,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral150 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral151 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral152 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral153 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral154 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral155 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral156 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral157 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral158 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral159 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral160 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral161 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral162 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral163 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral164 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral165 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral166 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral167 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral168 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,8,9,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral169 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral170 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral171 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral172 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral173 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral174 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral175 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral176 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral177 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral178 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral179 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral180 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral181 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral182 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral183 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral184 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral185 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,8,9,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral186 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral187 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral188 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral189 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral190 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral191 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
