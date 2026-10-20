import SymmetricSubgroupAsymptotics.FiniteGroupCertificates

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

def alphaTargetLiteral192 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral193 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral194 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral195 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral196 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral197 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral198 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral199 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral200 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral201 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral202 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral203 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral204 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral205 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral206 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral207 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral208 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral209 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral210 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral211 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral212 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral213 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral214 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral215 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral216 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral217 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral218 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral219 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral220 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral221 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral222 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral223 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral224 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral225 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral226 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral227 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral228 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral229 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral230 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral231 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral232 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral233 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral234 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral235 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral236 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral237 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral238 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral239 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral240 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral241 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral242 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral243 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral244 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral245 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral246 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral247 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral248 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral249 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral250 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral251 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral252 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral253 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral254 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaTargetLiteral255 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
