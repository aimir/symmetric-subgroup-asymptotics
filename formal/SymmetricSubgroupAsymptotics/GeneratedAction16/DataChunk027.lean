import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
864 through 895. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node998Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node998Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,9,8,11,10,5,4,7,6,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,9,8,11,10,5,4,7,6,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node998Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,7,6,4,5,9,8,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,6,7,5,4,9,8,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node998Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,12,13,15,14,1,0,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,14,15,12,13,2,3,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node998Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node998Generator0 else node998Generator1) else (if j.val < 3 then node998Generator2 else node998Generator3))

def node999Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,15,14,12,13,10,11,9,8,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,14,15,13,12,11,10,8,9,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node999Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,0,1,2,3,7,6,4,5,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,10,11,9,8,14,15,12,13,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node999Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node999Generator0 else node999Generator1)

def node1000Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1000Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,10,11,9,8,6,7,4,5,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,10,11,8,9,7,6,4,5,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1000Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,9,8,10,11,4,5,7,6,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,8,9,11,10,5,4,6,7,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1000Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1000Generator0 else (if j.val < 2 then node1000Generator1 else node1000Generator2))

def node1001Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,0,1,3,2,14,15,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,3,2,1,0,13,12,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1001Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,10,11,8,9,15,14,12,13,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,0,1,3,2,6,7,4,5,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1001Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,8,9,10,11,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,10,11,9,8,4,5,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1001Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1001Generator0 else (if j.val < 2 then node1001Generator1 else node1001Generator2))

def node1002Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,3,2,15,14,12,13,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,2,3,12,13,14,15,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1002Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,10,11,9,8,6,7,5,4,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,11,10,8,9,7,6,4,5,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1002Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,6,7,5,4,10,11,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,7,6,4,5,10,11,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1002Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1002Generator0 else (if j.val < 2 then node1002Generator1 else node1002Generator2))

def node1003Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,10,11,8,9,5,4,7,6,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,9,8,11,10,6,7,4,5,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1003Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,9,8,15,14,12,13,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,9,8,15,14,12,13,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1003Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,7,6,0,1,8,9,15,14,13,12,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,0,1,2,3,5,4,8,9,15,14,13,12,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1003Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1003Generator0 else (if j.val < 2 then node1003Generator1 else node1003Generator2))

def node1004Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,1,0,3,2,5,4,6,7,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,9,8,10,11,12,13,14,15,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1004Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,1,0,2,3,4,5,6,7,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,8,9,10,11,15,14,13,12,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1004Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1004Generator0 else node1004Generator1)

def node1005Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,0,1,3,2,5,4,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,5,4,7,6,1,0,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1005Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,15,14,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1005Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,0,1,7,6,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,0,1,7,6,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1005Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1005Generator0 else (if j.val < 2 then node1005Generator1 else node1005Generator2))

def node1006Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,9,8,11,10,15,14,12,13,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,1,0,3,2,5,4,7,6,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1006Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,12,13,15,14,11,10,9,8,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,13,12,14,15,11,10,9,8,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1006Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,9,8,11,10,4,5,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,8,9,10,11,5,4,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1006Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1006Generator0 else (if j.val < 2 then node1006Generator1 else node1006Generator2))

def node1007Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,2,3,13,12,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,3,2,12,13,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1007Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,5,4,7,6,3,2,1,0,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,5,4,7,6,2,3,0,1,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1007Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1007Generator0 else node1007Generator1)

def node1008Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,1,0,3,2,15,14,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,3,2,1,0,12,13,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1008Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,9,8,10,11,4,5,6,7,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,8,9,10,11,5,4,6,7,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1008Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,7,6,5,4,10,11,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,7,6,5,4,10,11,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1008Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1008Generator0 else (if j.val < 2 then node1008Generator1 else node1008Generator2))

def node1009Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,8,9,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,8,9,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1009Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,13,12,14,15,0,1,2,3,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,14,15,13,12,2,3,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1009Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1009Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1009Generator0 else (if j.val < 2 then node1009Generator1 else node1009Generator2))

def node1010Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,3,2,12,13,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,2,3,12,13,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1010Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,13,12,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1010Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,7,6,4,5,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,6,7,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1010Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1010Generator0 else (if j.val < 2 then node1010Generator1 else node1010Generator2))

def node1011Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1011Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,0,1,2,3,5,4,7,6,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,9,8,11,10,12,13,14,15,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1011Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,2,3,0,1,15,14,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,0,1,3,2,12,13,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1011Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1011Generator0 else (if j.val < 2 then node1011Generator1 else node1011Generator2))

def node1012Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,14,15,13,12,11,10,9,8,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,15,14,12,13,11,10,9,8,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1012Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,2,3,1,0,5,4,7,6,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,9,8,11,10,13,12,14,15,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1012Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,9,8,11,10,4,5,6,7,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,8,9,10,11,5,4,7,6,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1012Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1012Generator0 else (if j.val < 2 then node1012Generator1 else node1012Generator2))

def node1013Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,13,12,14,15,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,12,13,14,15,3,2,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1013Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,2,3,0,1,14,15,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,0,1,3,2,12,13,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1013Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,7,6,5,4,11,10,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1013Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1013Generator0 else (if j.val < 2 then node1013Generator1 else node1013Generator2))

def node1014Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,8,9,11,10,5,4,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,9,8,10,11,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1014Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,9,8,11,10,6,7,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,11,10,8,9,5,4,7,6,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1014Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,4,5,6,7,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,4,5,6,7,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1014Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1014Generator0 else (if j.val < 2 then node1014Generator1 else node1014Generator2))

def node1015Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,1,0,2,3,12,13,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,3,2,1,0,14,15,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1015Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,1,0,15,14,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,0,1,14,15,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1015Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,14,15,3,2,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,12,13,0,1,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1015Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1015Generator0 else (if j.val < 2 then node1015Generator1 else node1015Generator2))

def node1016Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,12,13,15,14,11,10,9,8,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,12,13,15,14,11,10,9,8,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1016Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,10,11,9,8,13,12,15,14,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,2,3,1,0,7,6,4,5,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1016Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,2,3,0,1,5,4,7,6,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,9,8,11,10,15,14,12,13,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1016Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1016Generator0 else (if j.val < 2 then node1016Generator1 else node1016Generator2))

def node1017Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,3,2,1,0,5,4,7,6,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,9,8,11,10,15,14,12,13,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1017Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,15,14,13,12,10,11,9,8,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,12,13,14,15,11,10,8,9,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1017Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,4,5,7,6,8,9,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,4,5,7,6,8,9,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1017Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1017Generator0 else (if j.val < 2 then node1017Generator1 else node1017Generator2))

def node1018Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,8,9,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,8,9,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1018Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,1,0,3,2,6,7,4,5,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,10,11,8,9,12,13,14,15,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1018Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1018Generator0 else node1018Generator1)

def node1019Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,11,10,8,9,13,12,14,15,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,1,0,3,2,6,7,5,4,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1019Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,5,4,8,9,10,11,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,4,5,8,9,10,11,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1019Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1019Generator0 else node1019Generator1)

def node1020Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,3,2,1,0,12,13,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,0,1,2,3,12,13,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1020Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,15,14,13,12,3,2,1,0,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,13,12,14,15,2,3,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1020Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1020Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1020Generator0 else (if j.val < 2 then node1020Generator1 else node1020Generator2))

def node1021Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1021Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,0,1,3,2,14,15,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,2,3,0,1,13,12,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1021Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,8,9,10,11,4,5,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,8,9,10,11,4,5,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1021Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1021Generator0 else (if j.val < 2 then node1021Generator1 else node1021Generator2))

def node1022Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1022Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,12,13,11,10,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,12,13,11,10,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1022Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,8,9,10,11,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,4,5,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1022Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1022Generator0 else (if j.val < 2 then node1022Generator1 else node1022Generator2))

def node1023Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,10,11,8,9,5,4,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,9,8,11,10,6,7,4,5,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1023Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,4,5,7,6,8,9,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,4,5,7,6,8,9,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1023Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,15,14,12,13,0,1,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,15,14,12,13,0,1,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1023Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1023Generator0 else (if j.val < 2 then node1023Generator1 else node1023Generator2))

def node1024Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,7,6,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,6,7,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1024Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,1,0,3,2,13,12,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,2,3,1,0,15,14,13,12,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1024Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,10,11,9,8,5,4,7,6,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,9,8,11,10,7,6,4,5,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1024Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1024Generator0 else (if j.val < 2 then node1024Generator1 else node1024Generator2))

def node1025Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1025Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1025Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,15,14,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1025Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1025Generator0 else (if j.val < 2 then node1025Generator1 else node1025Generator2))

def node1026Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,8,9,11,10,14,15,13,12,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,3,2,1,0,4,5,7,6,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1026Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,12,13,14,15,3,2,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,12,13,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1026Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1026Generator0 else node1026Generator1)

def node1082Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1082Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1082Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1082Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1082Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,14,15,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,14,15,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1082Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,3,2,8,9,7,6,12,13,10,11,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,5,4,2,3,9,8,6,7,12,13,10,11,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1082Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node1082Generator0 else (if j.val < 2 then node1082Generator1 else node1082Generator2)) else (if j.val < 4 then node1082Generator3 else (if j.val < 5 then node1082Generator4 else node1082Generator5)))

def node1083Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1083Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1083Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1083Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1083Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1083Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,2,3,0,1,15,14,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,1,0,3,2,12,13,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1083Generator6 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1083Generators (j : Fin 7) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node1083Generator0 else (if j.val < 2 then node1083Generator1 else node1083Generator2)) else (if j.val < 5 then (if j.val < 4 then node1083Generator3 else node1083Generator4) else (if j.val < 6 then node1083Generator5 else node1083Generator6)))

def node1084Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1084Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,4,5,11,10,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,5,4,10,11,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1084Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1084Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1084Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1084Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,2,3,0,1,12,13,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,1,0,2,3,14,15,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1084Generator6 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1084Generators (j : Fin 7) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node1084Generator0 else (if j.val < 2 then node1084Generator1 else node1084Generator2)) else (if j.val < 5 then (if j.val < 4 then node1084Generator3 else node1084Generator4) else (if j.val < 6 then node1084Generator5 else node1084Generator6)))

end SymmetricSubgroupAsymptotics.BinaryActionData16
