import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
0 through 31. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node1Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,9,8,10,11,13,12,14,15,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,0,1,3,2,4,5,7,6,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1Generators (j : Fin 1) : Equiv.Perm (Fin 16) :=
  node1Generator0

def node2Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,13,12,15,14,0,1,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,13,12,15,14,0,1,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node2Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,0,1,10,11,13,12,6,7,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,15,14,0,1,10,11,13,12,6,7,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node2Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,8,9,11,10,4,5,14,15,0,1,2,3,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,6,7,1,0,2,3,5,4,14,15,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node2Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node2Generator0 else (if j.val < 2 then node2Generator1 else node2Generator2))

def node3Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node3Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node3Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,14,15,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,14,15,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node3Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,2,3,9,8,7,6,13,12,11,10,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,4,5,2,3,9,8,7,6,13,12,11,10,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node3Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node3Generator0 else node3Generator1) else (if j.val < 3 then node3Generator2 else node3Generator3))

def node4Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,8,9,10,11,4,5,14,15,0,1,2,3,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,6,7,0,1,2,3,4,5,14,15,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node4Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,7,6,8,9,2,3,5,4,14,15,1,0,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,6,7,9,8,3,2,4,5,15,14,0,1,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node4Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node4Generator0 else node4Generator1)

def node5Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,0,1,2,3,4,5,6,7,9,8,11,10,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,4,5,6,7,8,9,11,10,13,12,14,15,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node5Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,5,4,7,6,9,8,10,11,12,13,15,14,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,1,0,3,2,5,4,7,6,8,9,10,11,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node5Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node5Generator0 else node5Generator1)

def node6Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,7,6,8,9,10,11,12,13,15,14,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,0,1,2,3,5,4,6,7,8,9,10,11,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node6Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,3,2,12,13,7,6,0,1,11,10,4,5,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,3,2,12,13,7,6,0,1,11,10,4,5,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node6Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node6Generator0 else node6Generator1)

def node7Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,3,2,9,8,6,7,13,12,10,11,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,5,4,2,3,8,9,7,6,12,13,11,10,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node7Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,7,6,9,8,2,3,4,5,15,14,0,1,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,6,7,8,9,3,2,5,4,14,15,1,0,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node7Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,14,15,1,0,11,10,13,12,7,6,9,8,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,14,15,1,0,11,10,13,12,7,6,9,8,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node7Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node7Generator0 else (if j.val < 2 then node7Generator1 else node7Generator2))

def node8Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,0,1,3,2,13,12,6,7,8,9,11,10,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,5,4,15,14,8,9,10,11,13,12,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node8Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,8,9,10,11,4,5,14,15,1,0,3,2,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,6,7,1,0,2,3,4,5,15,14,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node8Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node8Generator0 else node8Generator1)

def node9Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,14,15,10,11,12,13,6,7,8,9,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,14,15,10,11,12,13,6,7,8,9,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node9Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,7,6,2,3,4,5,15,14,1,0,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,6,7,8,9,5,4,3,2,0,1,14,15,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node9Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,7,6,9,8,3,2,5,4,14,15,0,1,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,7,6,9,8,3,2,5,4,14,15,0,1,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node9Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node9Generator0 else (if j.val < 2 then node9Generator1 else node9Generator2))

def node10Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,5,4,15,14,8,9,10,11,13,12,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,0,1,3,2,13,12,6,7,8,9,11,10,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node10Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,3,2,12,13,7,6,0,1,11,10,4,5,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,3,2,12,13,7,6,0,1,11,10,4,5,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node10Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node10Generator0 else node10Generator1)

def node11Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,9,8,11,10,12,13,14,15,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,0,1,2,3,5,4,7,6,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node11Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,11,10,9,8,14,15,12,13,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,2,3,0,1,7,6,5,4,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node11Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,3,2,12,13,7,6,0,1,11,10,4,5,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,3,2,12,13,7,6,0,1,11,10,4,5,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node11Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node11Generator0 else (if j.val < 2 then node11Generator1 else node11Generator2))

def node12Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,6,7,8,9,11,10,12,13,15,14,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,0,1,2,3,4,5,6,7,9,8,10,11,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node12Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,10,11,1,0,7,6,12,13,2,3,8,9,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,10,11,1,0,7,6,12,13,2,3,8,9,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node12Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node12Generator0 else node12Generator1)

def node13Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,6,7,8,9,10,11,12,13,15,14,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,1,0,2,3,4,5,6,7,8,9,10,11,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node13Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,7,6,5,4,3,2,0,1,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,7,6,5,4,3,2,0,1,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node13Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node13Generator0 else node13Generator1)

def node14Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,14,15,5,4,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,15,14,4,5,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node14Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,7,6,4,5,3,2,0,1,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,6,7,5,4,2,3,1,0,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node14Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node14Generator0 else node14Generator1)

def node15Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,14,15,9,8,2,3,12,13,6,7,1,0,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,6,7,0,1,10,11,5,4,14,15,8,9,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node15Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,1,0,11,10,5,4,14,15,8,9,2,3,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,12,13,7,6,1,0,10,11,5,4,14,15,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node15Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,11,10,5,4,15,14,9,8,3,2,13,12,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,11,10,5,4,15,14,9,8,3,2,13,12,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node15Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node15Generator0 else (if j.val < 2 then node15Generator1 else node15Generator2))

def node16Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,9,8,10,11,1,0,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,12,13,15,14,5,4,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node16Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node16Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,12,13,3,2,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,12,13,3,2,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node16Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node16Generator0 else (if j.val < 2 then node16Generator1 else node16Generator2))

def node17Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,6,7,1,0,10,11,4,5,14,15,8,9,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,14,15,8,9,2,3,12,13,6,7,1,0,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node17Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,11,10,5,4,15,14,9,8,3,2,13,12,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,11,10,5,4,15,14,9,8,3,2,13,12,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node17Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,3,2,8,9,7,6,12,13,11,10,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,5,4,2,3,9,8,6,7,13,12,10,11,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node17Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node17Generator0 else (if j.val < 2 then node17Generator1 else node17Generator2))

def node18Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node18Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,9,8,11,10,13,12,14,15,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,0,1,3,2,5,4,7,6,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node18Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,3,2,13,12,7,6,0,1,11,10,5,4,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,3,2,13,12,7,6,0,1,11,10,5,4,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node18Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,5,4,3,2,9,8,7,6,13,12,11,10,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,5,4,3,2,9,8,7,6,13,12,11,10,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node18Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node18Generator0 else node18Generator1) else (if j.val < 3 then node18Generator2 else node18Generator3))

def node19Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,6,7,8,9,4,5,2,3,0,1,15,14,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,6,7,2,3,4,5,15,14,0,1,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node19Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,6,7,5,4,3,2,1,0,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,7,6,4,5,2,3,0,1,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node19Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,15,14,0,1,10,11,12,13,7,6,9,8,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,14,15,1,0,11,10,13,12,6,7,8,9,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node19Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node19Generator0 else (if j.val < 2 then node19Generator1 else node19Generator2))

def node20Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node20Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node20Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node20Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,12,13,2,3,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,12,13,2,3,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node20Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node20Generator0 else node20Generator1) else (if j.val < 3 then node20Generator2 else node20Generator3))

def node21Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,0,1,10,11,12,13,6,7,8,9,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,15,14,0,1,10,11,12,13,6,7,8,9,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node21Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,6,7,8,9,3,2,5,4,14,15,1,0,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,7,6,9,8,2,3,4,5,15,14,0,1,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node21Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,6,7,2,3,4,5,15,14,0,1,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,6,7,8,9,4,5,2,3,0,1,15,14,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node21Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node21Generator0 else (if j.val < 2 then node21Generator1 else node21Generator2))

def node22Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,4,5,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,8,9,10,11,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node22Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,5,4,7,6,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,9,8,11,10,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node22Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node22Generator0 else node22Generator1)

def node23Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,5,4,3,2,6,7,8,9,13,12,11,10,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,5,4,3,2,6,7,8,9,13,12,11,10,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node23Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,4,5,2,3,8,9,6,7,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,4,5,2,3,8,9,6,7,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node23Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,14,15,0,1,11,10,13,12,7,6,9,8,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,14,15,0,1,11,10,13,12,7,6,9,8,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node23Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,15,14,1,0,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,12,13,15,14,1,0,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node23Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,5,4,3,2,9,8,7,6,13,12,11,10,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,5,4,3,2,9,8,7,6,13,12,11,10,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node23Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node23Generator0 else node23Generator1) else (if j.val < 3 then node23Generator2 else (if j.val < 4 then node23Generator3 else node23Generator4)))

def node24Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,6,7,9,8,11,10,13,12,15,14,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,0,1,2,3,4,5,7,6,9,8,11,10,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node24Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,3,2,13,12,7,6,1,0,11,10,5,4,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,3,2,13,12,7,6,1,0,11,10,5,4,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node24Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node24Generator0 else node24Generator1)

def node25Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,9,8,7,6,13,12,11,10,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,9,8,7,6,13,12,11,10,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node25Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,0,1,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,15,14,0,1,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node25Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node25Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,4,5,2,3,7,6,9,8,11,10,13,12,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,4,5,2,3,7,6,9,8,11,10,13,12,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node25Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node25Generator0 else node25Generator1) else (if j.val < 3 then node25Generator2 else node25Generator3))

def node26Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,0,1,14,15,13,12,11,10,9,8,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,0,1,14,15,13,12,11,10,9,8,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node26Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,15,14,12,13,10,11,9,8,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,14,15,13,12,11,10,8,9,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node26Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node26Generator0 else node26Generator1)

def node27Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node27Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,8,9,2,3,13,12,7,6,1,0,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,6,7,0,1,11,10,4,5,14,15,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node27Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,11,10,4,5,14,15,9,8,3,2,12,13,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,11,10,4,5,14,15,9,8,3,2,12,13,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node27Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node27Generator0 else (if j.val < 2 then node27Generator1 else node27Generator2))

def node28Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,9,8,10,11,5,4,15,14,0,1,3,2,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,7,6,0,1,3,2,4,5,14,15,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node28Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,9,8,10,11,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,5,4,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node28Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node28Generator0 else node28Generator1)

def node29Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node29Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,0,1,2,3,5,4,7,6,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,8,9,11,10,13,12,14,15,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node29Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,6,7,4,5,2,3,1,0,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,6,7,4,5,2,3,1,0,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node29Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node29Generator0 else (if j.val < 2 then node29Generator1 else node29Generator2))

def node30Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,7,6,9,8,5,4,3,2,1,0,14,15,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,7,6,3,2,5,4,14,15,1,0,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node30Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,0,1,13,12,11,10,9,8,7,6,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,15,14,0,1,13,12,11,10,9,8,7,6,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node30Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,15,14,12,13,10,11,9,8,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,14,15,13,12,11,10,8,9,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node30Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node30Generator0 else (if j.val < 2 then node30Generator1 else node30Generator2))

def node31Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,13,12,11,10,14,15,1,0,3,2,5,4,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,13,12,1,0,14,15,5,4,3,2,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node31Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,15,14,0,1,10,11,12,13,7,6,9,8,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,14,15,1,0,11,10,13,12,6,7,8,9,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node31Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,8,9,6,7,12,13,10,11,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,8,9,6,7,12,13,10,11,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node31Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node31Generator0 else (if j.val < 2 then node31Generator1 else node31Generator2))

def node32Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,2,3,7,6,8,9,10,11,13,12,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,4,5,2,3,7,6,8,9,10,11,13,12,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node32Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,7,6,8,9,5,4,3,2,0,1,15,14,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,7,6,3,2,4,5,15,14,1,0,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node32Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,14,15,1,0,11,10,13,12,7,6,9,8,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,14,15,1,0,11,10,13,12,7,6,9,8,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node32Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node32Generator0 else (if j.val < 2 then node32Generator1 else node32Generator2))

end SymmetricSubgroupAsymptotics.BinaryActionData16
