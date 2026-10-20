import SymmetricSubgroupAsymptotics.FiniteGroupCertificates

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

def alphaSourceLiteral256 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral257 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral258 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral259 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral260 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral261 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral262 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral263 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral264 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral265 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral266 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral267 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral268 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral269 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral270 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral271 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral272 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,15,14,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral273 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral274 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral275 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral276 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral277 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral278 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral279 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral280 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral281 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral282 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral283 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral284 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral285 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral286 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral287 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral288 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral289 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral290 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral291 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral292 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral293 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral294 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral295 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral296 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,9,8,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral297 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral298 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral299 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral300 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral301 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral302 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral303 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral304 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral305 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral306 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral307 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral308 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral309 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral310 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral311 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,12,13,10,11,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral312 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral313 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral314 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral315 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral316 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral317 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral318 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral319 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
