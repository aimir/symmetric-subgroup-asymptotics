import SymmetricSubgroupAsymptotics.FiniteGroupCertificates

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

def quotientElementLiteral192 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral193 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral194 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral195 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral196 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral197 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral198 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral199 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral200 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral201 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral202 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral203 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral204 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral205 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,6,4,7,5,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,5,7,4,6,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral206 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral207 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral208 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral209 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral210 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral211 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral212 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral213 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral214 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,7,5,6,4,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,7,5,6,4,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral215 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,4,6,5,7,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,4,6,5,7,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral216 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral217 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral218 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,8,10,9,11,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral219 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral220 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral221 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral222 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral223 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral224 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral225 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral226 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral227 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral228 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral229 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral230 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral231 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral232 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral233 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral234 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral235 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral236 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral237 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral238 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral239 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral240 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral241 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,7,5,6,4,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,7,5,6,4,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral242 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,4,6,5,7,8,10,9,11,13,15,12,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,4,6,5,7,8,10,9,11,14,12,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral243 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,15,13,14,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,15,13,14,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral244 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral245 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,9,11,8,10,12,14,13,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,10,8,11,9,12,14,13,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral246 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,0,1,2,5,7,4,6,10,8,11,9,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,2,3,0,6,4,7,5,9,11,8,10,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral247 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral248 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral249 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral250 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral251 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral252 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral253 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral254 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,2,3,0,5,7,4,6,11,9,10,8,14,12,15,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,0,1,2,6,4,7,5,11,9,10,8,13,15,12,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def quotientElementLiteral255 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
