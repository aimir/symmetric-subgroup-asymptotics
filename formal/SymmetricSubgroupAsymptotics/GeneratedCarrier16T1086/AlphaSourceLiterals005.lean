import SymmetricSubgroupAsymptotics.FiniteGroupCertificates

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

def alphaSourceLiteral320 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,11,10,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral321 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral322 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral323 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,10,11,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,0,1,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral324 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral325 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral326 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral327 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral328 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral329 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral330 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral331 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral332 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral333 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral334 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral335 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral336 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral337 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,8,9,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral338 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral339 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral340 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral341 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral342 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral343 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral344 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral345 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral346 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral347 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral348 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral349 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral350 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral351 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral352 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral353 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral354 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral355 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral356 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral357 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral358 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral359 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral360 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral361 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral362 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral363 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral364 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral365 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral366 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,15,14,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral367 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral368 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,13,12,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral369 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral370 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral371 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral372 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral373 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral374 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,8,9,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral375 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral376 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral377 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,4,5,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,15,14,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral378 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral379 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,10,11,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral380 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral381 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral382 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def alphaSourceLiteral383 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,12,13,0,1,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,10,11,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel


end SymmetricSubgroupAsymptotics.BinaryChart16T1086
