import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
224 through 255. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node254Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,8,9,5,4,7,6,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,9,8,11,10,6,7,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node254Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,12,13,11,10,8,9,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,12,13,11,10,8,9,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node254Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,13,12,10,11,9,8,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,13,12,10,11,9,8,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node254Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node254Generator0 else (if j.val < 2 then node254Generator1 else node254Generator2))

def node255Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,7,6,4,5,3,2,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,7,6,4,5,3,2,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node255Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,7,6,0,1,15,14,8,9,10,11,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,1,0,2,3,5,4,10,11,12,13,15,14,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node255Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node255Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,15,14,4,5,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,14,15,5,4,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node255Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node255Generator0 else node255Generator1) else (if j.val < 3 then node255Generator2 else node255Generator3))

def node256Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,9,8,5,4,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,9,8,11,10,7,6,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node256Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,0,1,7,6,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,0,1,7,6,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node256Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,13,12,10,11,9,8,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,13,12,10,11,9,8,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node256Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node256Generator0 else (if j.val < 2 then node256Generator1 else node256Generator2))

def node257Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,4,5,6,7,0,1,2,3,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,6,7,8,9,3,2,4,5,14,15,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node257Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,10,11,13,12,15,14,8,9,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,14,15,0,1,3,2,12,13,6,7,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node257Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node257Generator0 else node257Generator1)

def node258Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,9,8,11,10,4,5,15,14,0,1,3,2,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,6,7,0,1,3,2,5,4,14,15,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node258Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,0,1,10,11,12,13,7,6,9,8,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,12,13,14,15,9,8,11,10,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node258Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node258Generator0 else node258Generator1)

def node259Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,11,10,4,5,14,15,8,9,3,2,12,13,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,11,10,4,5,14,15,8,9,3,2,12,13,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node259Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,10,11,13,12,14,15,8,9,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,10,11,13,12,14,15,8,9,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node259Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,8,9,11,10,4,5,14,15,1,0,2,3,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,6,7,0,1,2,3,5,4,14,15,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node259Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node259Generator0 else (if j.val < 2 then node259Generator1 else node259Generator2))

def node260Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,7,6,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,9,8,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node260Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,13,12,2,3,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,13,12,2,3,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node260Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node260Generator0 else node260Generator1)

def node261Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,8,9,11,10,12,13,14,15,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,0,1,2,3,5,4,6,7,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node261Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,9,8,10,11,13,12,14,15,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,1,0,3,2,5,4,6,7,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node261Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,2,3,4,5,6,7,1,0,11,10,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,4,5,6,7,8,9,2,3,13,12,14,15,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node261Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node261Generator0 else (if j.val < 2 then node261Generator1 else node261Generator2))

def node262Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node262Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node262Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,15,14,13,12,1,0,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,14,15,12,13,0,1,2,3,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node262Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,5,4,6,7,8,9,11,10,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,5,4,6,7,8,9,11,10,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node262Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node262Generator0 else node262Generator1) else (if j.val < 3 then node262Generator2 else node262Generator3))

def node263Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,11,10,9,8,12,13,14,15,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,3,2,0,1,7,6,5,4,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node263Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,15,14,12,13,3,2,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,13,12,3,2,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node263Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node263Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node263Generator0 else (if j.val < 2 then node263Generator1 else node263Generator2))

def node264Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node264Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node264Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,13,12,15,14,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,12,13,14,15,3,2,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node264Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,4,5,6,7,9,8,11,10,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,4,5,6,7,9,8,11,10,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node264Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node264Generator0 else node264Generator1) else (if j.val < 3 then node264Generator2 else node264Generator3))

def node265Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,13,12,15,14,8,9,10,11,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,13,12,15,14,8,9,10,11,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node265Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node265Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,2,3,0,1,6,7,4,5,10,11,9,8,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,8,9,6,7,13,12,10,11,1,0,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node265Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,10,11,9,8,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,10,11,9,8,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node265Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node265Generator0 else node265Generator1) else (if j.val < 3 then node265Generator2 else node265Generator3))

def node266Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,10,11,9,8,3,2,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,13,12,7,6,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node266Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,11,10,9,8,2,3,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,14,15,12,13,7,6,5,4,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node266Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,8,9,10,11,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,12,13,14,15,4,5,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node266Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node266Generator0 else (if j.val < 2 then node266Generator1 else node266Generator2))

def node267Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,8,9,11,10,7,6,5,4,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,11,10,9,8,4,5,7,6,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node267Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,7,6,5,4,10,11,8,9,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,7,6,5,4,10,11,8,9,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node267Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,2,3,0,1,15,14,12,13,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,0,1,3,2,12,13,14,15,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node267Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node267Generator0 else (if j.val < 2 then node267Generator1 else node267Generator2))

def node268Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node268Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,8,9,11,10,6,7,5,4,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,11,10,8,9,4,5,7,6,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node268Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node268Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node268Generator0 else (if j.val < 2 then node268Generator1 else node268Generator2))

def node269Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node269Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node269Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,15,14,13,12,1,0,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,14,15,12,13,0,1,2,3,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node269Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,5,4,6,7,8,9,11,10,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,5,4,6,7,8,9,11,10,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node269Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node269Generator0 else node269Generator1) else (if j.val < 3 then node269Generator2 else node269Generator3))

def node270Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node270Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node270Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node270Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node270Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,14,15,12,13,1,0,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,14,15,12,13,1,0,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node270Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node270Generator0 else node270Generator1) else (if j.val < 3 then node270Generator2 else (if j.val < 4 then node270Generator3 else node270Generator4)))

def node271Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,8,9,6,7,12,13,10,11,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,8,9,6,7,12,13,10,11,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node271Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,14,15,5,4,9,8,11,10,13,12,7,6,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,14,15,5,4,13,12,7,6,9,8,11,10,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node271Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,14,15,0,1,7,6,9,8,11,10,13,12,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,14,15,0,1,7,6,9,8,11,10,13,12,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node271Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,14,15,0,1,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,14,15,0,1,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node271Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node271Generator0 else node271Generator1) else (if j.val < 3 then node271Generator2 else node271Generator3))

def node272Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node272Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,15,14,12,13,7,6,5,4,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,11,10,9,8,2,3,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node272Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,4,5,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,8,9,10,11,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node272Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node272Generator0 else (if j.val < 2 then node272Generator1 else node272Generator2))

def node273Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,1,0,3,2,4,5,14,15,8,9,10,11,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,5,4,6,7,0,1,10,11,12,13,14,15,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node273Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,8,9,11,10,4,5,14,15,1,0,2,3,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,6,7,0,1,2,3,5,4,14,15,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node273Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,3,2,13,12,14,15,1,0,11,10,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,3,2,13,12,14,15,1,0,11,10,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node273Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node273Generator0 else (if j.val < 2 then node273Generator1 else node273Generator2))

def node274Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node274Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,11,10,5,4,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,9,8,10,11,0,1,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node274Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,15,14,12,13,2,3,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,13,12,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node274Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node274Generator0 else (if j.val < 2 then node274Generator1 else node274Generator2))

def node275Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,9,8,10,11,1,0,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,10,11,5,4,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node275Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node275Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,11,10,8,9,2,3,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,13,12,6,7,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node275Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node275Generator0 else (if j.val < 2 then node275Generator1 else node275Generator2))

def node276Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node276Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node276Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node276Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,12,13,2,3,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,12,13,2,3,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node276Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node276Generator0 else node276Generator1) else (if j.val < 3 then node276Generator2 else node276Generator3))

def node277Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node277Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node277Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node277Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,15,14,4,5,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,14,15,5,4,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node277Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node277Generator0 else node277Generator1) else (if j.val < 3 then node277Generator2 else node277Generator3))

def node278Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node278Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,15,14,12,13,2,3,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,13,12,15,14,0,1,2,3,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node278Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,10,11,8,9,5,4,6,7,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,9,8,10,11,6,7,4,5,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node278Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node278Generator0 else (if j.val < 2 then node278Generator1 else node278Generator2))

def node279Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,11,10,8,9,4,5,6,7,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,8,9,10,11,6,7,5,4,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node279Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node279Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,13,12,14,15,1,0,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,14,15,12,13,2,3,1,0,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node279Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node279Generator0 else (if j.val < 2 then node279Generator1 else node279Generator2))

def node280Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,12,13,14,15,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node280Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,14,15,13,12,1,0,2,3,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,15,14,12,13,1,0,2,3,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node280Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,10,11,9,8,6,7,5,4,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,11,10,8,9,7,6,4,5,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node280Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node280Generator0 else (if j.val < 2 then node280Generator1 else node280Generator2))

def node281Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,5,4,6,7,8,9,11,10,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,5,4,6,7,8,9,11,10,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node281Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,14,15,13,12,1,0,2,3,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,0,1,3,2,14,15,13,12,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node281Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node281Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node281Generator0 else (if j.val < 2 then node281Generator1 else node281Generator2))

def node282Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node282Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,7,6,9,8,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,7,6,9,8,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node282Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,13,12,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,14,15,13,12,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node282Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,9,8,10,11,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,5,4,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node282Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node282Generator0 else node282Generator1) else (if j.val < 3 then node282Generator2 else node282Generator3))

def node283Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node283Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,0,1,7,6,12,13,11,10,8,9,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,0,1,7,6,12,13,11,10,8,9,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node283Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,10,11,9,8,7,6,13,12,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,2,3,9,8,7,6,4,5,11,10,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node283Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node283Generator0 else (if j.val < 2 then node283Generator1 else node283Generator2))

def node284Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node284Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node284Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,13,12,15,14,3,2,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,13,12,15,14,3,2,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node284Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node284Generator0 else (if j.val < 2 then node284Generator1 else node284Generator2))

def node285Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node285Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,5,4,6,7,10,11,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,5,4,6,7,10,11,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node285Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,3,2,0,1,7,6,5,4,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,11,10,9,8,13,12,15,14,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node285Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node285Generator0 else (if j.val < 2 then node285Generator1 else node285Generator2))

end SymmetricSubgroupAsymptotics.BinaryActionData16
