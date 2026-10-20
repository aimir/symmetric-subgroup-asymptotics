import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
608 through 639. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node672Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,15,14,13,12,0,1,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,15,14,3,2,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node672Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,9,8,5,4,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,15,14,7,6,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node672Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,14,15,4,5,7,6,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,8,9,11,10,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node672Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node672Generator0 else (if j.val < 2 then node672Generator1 else node672Generator2))

def node673Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,11,10,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,10,11,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node673Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,10,11,8,9,2,3,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,15,14,13,12,6,7,4,5,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node673Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node673Generator0 else node673Generator1)

def node674Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,15,14,4,5,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,14,15,5,4,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node674Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,14,15,2,3,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,12,13,4,5,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node674Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,0,1,2,3,4,5,15,14,8,9,10,11,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,4,5,6,7,1,0,10,11,12,13,14,15,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node674Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node674Generator0 else (if j.val < 2 then node674Generator1 else node674Generator2))

def node675Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,9,8,10,11,1,0,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,12,13,15,14,5,4,6,7,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node675Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,10,11,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,11,10,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node675Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node675Generator0 else node675Generator1)

def node676Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,11,10,9,8,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,11,10,9,8,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node676Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,10,11,8,9,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,10,11,8,9,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node676Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,15,14,13,12,1,0,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,15,14,13,12,1,0,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node676Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node676Generator0 else (if j.val < 2 then node676Generator1 else node676Generator2))

def node677Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,0,1,7,6,11,10,12,13,15,14,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,0,1,7,6,15,14,9,8,10,11,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node677Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,13,12,3,2,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,13,12,3,2,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node677Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node677Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node677Generator0 else (if j.val < 2 then node677Generator1 else node677Generator2))

def node678Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,13,12,15,14,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,12,13,14,15,2,3,0,1,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node678Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,7,6,5,4,11,10,9,8,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,7,6,5,4,11,10,9,8,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node678Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node678Generator0 else node678Generator1)

def node679Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,9,8,15,14,12,13,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,9,8,15,14,12,13,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node679Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,0,1,2,3,5,4,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,4,5,7,6,0,1,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node679Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,11,10,5,4,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,14,15,1,0,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node679Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node679Generator0 else (if j.val < 2 then node679Generator1 else node679Generator2))

def node680Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,14,15,13,12,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,3,2,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node680Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node680Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node680Generator0 else node680Generator1)

def node681Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,9,8,10,11,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,5,4,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node681Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,9,8,11,10,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,5,4,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node681Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node681Generator0 else node681Generator1)

def node682Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,3,2,0,1,13,12,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,1,0,3,2,13,12,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node682Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node682Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,6,7,5,4,9,8,10,11,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,7,6,4,5,9,8,10,11,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node682Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node682Generator0 else (if j.val < 2 then node682Generator1 else node682Generator2))

def node683Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,15,14,13,12,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node683Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,7,6,0,1,13,12,10,11,9,8,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,0,1,2,3,5,4,13,12,10,11,9,8,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node683Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node683Generator0 else node683Generator1)

def node684Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,9,8,10,11,4,5,6,7,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,8,9,10,11,5,4,6,7,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node684Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,6,7,5,4,3,2,0,1,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,7,6,4,5,2,3,1,0,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node684Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node684Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node684Generator0 else (if j.val < 2 then node684Generator1 else node684Generator2))

def node685Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,6,7,0,1,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,1,0,2,3,4,5,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node685Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,9,8,10,11,7,6,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,10,11,9,8,5,4,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node685Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node685Generator0 else node685Generator1)

def node686Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,10,11,9,8,2,3,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,15,14,12,13,7,6,4,5,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node686Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,10,11,9,8,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,11,10,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node686Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node686Generator0 else node686Generator1)

def node687Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node687Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,12,13,0,1,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,15,14,3,2,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node687Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,14,15,8,9,10,11,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,10,11,12,13,15,14,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node687Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node687Generator0 else (if j.val < 2 then node687Generator1 else node687Generator2))

def node688Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,5,4,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,9,8,10,11,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node688Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node688Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node688Generator0 else node688Generator1)

def node689Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,12,13,14,15,8,9,10,11,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,1,0,10,11,12,13,6,7,8,9,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node689Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,10,11,0,1,7,6,5,4,2,3,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,12,13,11,10,9,8,15,14,4,5,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node689Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,3,2,4,5,7,6,0,1,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,3,2,4,5,7,6,0,1,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node689Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node689Generator0 else (if j.val < 2 then node689Generator1 else node689Generator2))

def node690Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,6,7,1,0,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,0,1,2,3,4,5,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node690Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,9,8,3,2,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,12,13,7,6,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node690Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node690Generator0 else node690Generator1)

def node691Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,5,4,6,7,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,5,4,6,7,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node691Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,13,12,7,6,5,4,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,11,10,9,8,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node691Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node691Generator0 else node691Generator1)

def node692Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,15,14,7,6,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,9,8,5,4,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node692Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,8,9,10,11,2,3,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,12,13,4,5,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node692Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node692Generator0 else node692Generator1)

def node693Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,1,0,2,3,4,5,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,4,5,6,7,0,1,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node693Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node693Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,9,8,11,10,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,14,15,5,4,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node693Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node693Generator0 else (if j.val < 2 then node693Generator1 else node693Generator2))

def node694Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,15,14,8,9,10,11,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,10,11,12,13,14,15,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node694Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,14,15,6,7,5,4,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,11,10,8,9,0,1,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node694Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node694Generator0 else node694Generator1)

def node695Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,15,14,12,13,1,0,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,14,15,13,12,1,0,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node695Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,11,10,8,9,7,6,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,10,11,9,8,6,7,5,4,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node695Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node695Generator0 else node695Generator1)

def node696Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,7,6,5,4,3,2,12,13,11,10,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,7,6,5,4,3,2,12,13,11,10,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node696Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node696Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,12,13,3,2,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,12,13,3,2,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node696Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node696Generator0 else (if j.val < 2 then node696Generator1 else node696Generator2))

def node697Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,14,15,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node697Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,8,9,11,10,7,6,5,4,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,11,10,9,8,4,5,7,6,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node697Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node697Generator0 else node697Generator1)

def node698Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,9,8,10,11,6,7,5,4,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,11,10,8,9,5,4,6,7,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node698Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,15,14,12,13,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,15,14,2,3,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node698Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node698Generator0 else node698Generator1)

def node699Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,15,14,6,7,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,11,10,8,9,4,5,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node699Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node699Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node699Generator0 else node699Generator1)

def node700Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,15,14,5,4,11,10,9,8,7,6,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,13,12,11,10,9,8,15,14,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node700Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,6,7,5,4,2,3,1,0,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,7,6,4,5,3,2,0,1,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node700Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,15,14,8,9,10,11,12,13,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,0,1,2,3,13,12,6,7,8,9,10,11,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node700Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node700Generator0 else (if j.val < 2 then node700Generator1 else node700Generator2))

def node701Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,1,0,2,3,5,4,7,6,8,9,10,11,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,4,5,7,6,9,8,10,11,12,13,15,14,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node701Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,11,10,4,5,6,7,8,9,3,2,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,11,10,4,5,6,7,8,9,3,2,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node701Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,9,8,15,14,4,5,10,11,0,1,7,6,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,1,0,6,7,13,12,3,2,8,9,14,15,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node701Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node701Generator0 else (if j.val < 2 then node701Generator1 else node701Generator2))

def node702Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,12,13,0,1,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,12,13,11,10,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node702Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node702Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node702Generator0 else node702Generator1)

def node703Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,11,10,9,8,13,12,14,15,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,2,3,1,0,7,6,5,4,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node703Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,13,12,15,14,11,10,8,9,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,12,13,14,15,10,11,9,8,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node703Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,10,11,9,8,13,12,15,14,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,3,2,1,0,7,6,4,5,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node703Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node703Generator0 else (if j.val < 2 then node703Generator1 else node703Generator2))

end SymmetricSubgroupAsymptotics.BinaryActionData16
