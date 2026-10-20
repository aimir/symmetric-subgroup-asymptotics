import SymmetricSubgroupAsymptotics.FiniteGroupCertificates

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

def quotientElementLiteral128 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral129 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral130 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral131 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral132 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral133 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral134 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral135 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral136 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral137 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral138 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral139 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral140 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral141 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral142 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral143 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral144 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral145 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral146 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral147 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral148 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral149 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral150 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral151 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral152 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral153 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral154 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral155 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral156 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral157 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral158 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral159 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral160 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral161 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral162 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral163 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral164 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral165 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral166 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral167 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral168 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral169 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral170 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral171 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral172 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral173 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral174 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral175 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral176 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral177 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral178 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral179 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral180 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral181 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral182 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral183 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral184 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral185 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral186 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral187 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral188 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral189 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral190 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral191 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
