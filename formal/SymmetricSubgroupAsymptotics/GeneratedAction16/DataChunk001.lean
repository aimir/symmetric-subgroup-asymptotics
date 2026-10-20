import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
32 through 63. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node33Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,6,7,12,13,0,1,2,3,4,5,14,15,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,8,9,10,11,2,3,0,1,14,15,4,5,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node33Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,6,7,1,0,14,15,5,4,2,3,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,12,13,11,10,4,5,3,2,0,1,15,14,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node33Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node33Generator0 else node33Generator1)

def node34Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,2,3,7,6,9,8,10,11,12,13,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,4,5,2,3,7,6,9,8,10,11,12,13,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node34Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,6,7,2,3,4,5,15,14,0,1,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,6,7,8,9,4,5,2,3,0,1,15,14,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node34Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,1,0,14,15,5,4,3,2,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,13,12,11,10,14,15,1,0,3,2,5,4,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node34Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node34Generator0 else (if j.val < 2 then node34Generator1 else node34Generator2))

def node35Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,7,6,8,9,11,10,12,13,15,14,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,1,0,2,3,5,4,6,7,9,8,10,11,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node35Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,2,3,12,13,6,7,0,1,10,11,4,5,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,2,3,12,13,6,7,0,1,10,11,4,5,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node35Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,6,7,4,5,2,3,0,1,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,6,7,4,5,2,3,0,1,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node35Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node35Generator0 else (if j.val < 2 then node35Generator1 else node35Generator2))

def node36Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,10,11,12,13,7,6,9,8,2,3,4,5,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,10,11,12,13,7,6,9,8,2,3,4,5,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node36Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,5,4,6,7,8,9,10,11,13,12,14,15,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,0,1,3,2,4,5,6,7,8,9,11,10,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node36Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node36Generator0 else node36Generator1)

def node37Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,13,12,11,10,14,15,1,0,2,3,4,5,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,12,13,0,1,15,14,5,4,3,2,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node37Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,15,14,11,10,13,12,6,7,8,9,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,14,15,10,11,12,13,7,6,9,8,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node37Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,5,4,3,2,6,7,8,9,11,10,13,12,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,5,4,3,2,6,7,8,9,11,10,13,12,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node37Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node37Generator0 else (if j.val < 2 then node37Generator1 else node37Generator2))

def node38Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,6,7,8,9,11,10,12,13,14,15,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,1,0,2,3,4,5,6,7,9,8,10,11,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node38Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,3,2,12,13,7,6,0,1,11,10,4,5,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,3,2,12,13,7,6,0,1,11,10,4,5,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node38Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,7,6,5,4,3,2,1,0,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,7,6,5,4,3,2,1,0,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node38Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node38Generator0 else (if j.val < 2 then node38Generator1 else node38Generator2))

def node39Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,1,0,15,14,5,4,3,2,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,13,12,11,10,14,15,0,1,2,3,4,5,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node39Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,8,9,6,7,12,13,10,11,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,8,9,6,7,12,13,10,11,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node39Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,12,13,10,11,4,5,2,3,0,1,14,15,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,6,7,0,1,14,15,4,5,2,3,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node39Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node39Generator0 else (if j.val < 2 then node39Generator1 else node39Generator2))

def node40Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,9,8,4,5,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,14,15,7,6,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node40Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,12,13,0,1,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,10,11,2,3,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node40Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node40Generator0 else node40Generator1)

def node41Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,11,10,12,13,7,6,8,9,3,2,4,5,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,11,10,12,13,7,6,8,9,3,2,4,5,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node41Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,5,4,7,6,8,9,10,11,13,12,15,14,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,0,1,3,2,5,4,6,7,8,9,11,10,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node41Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node41Generator0 else node41Generator1)

def node42Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,14,15,7,6,9,8,11,10,13,12,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,0,1,2,3,7,6,9,8,11,10,13,12,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node42Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,13,12,15,14,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node42Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node42Generator0 else node42Generator1)

def node43Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,14,15,11,10,13,12,6,7,8,9,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,15,14,10,11,12,13,7,6,9,8,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node43Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,4,5,2,3,7,6,9,8,11,10,13,12,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,4,5,2,3,7,6,9,8,11,10,13,12,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node43Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,0,1,15,14,5,4,3,2,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,13,12,11,10,14,15,1,0,2,3,4,5,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node43Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node43Generator0 else (if j.val < 2 then node43Generator1 else node43Generator2))

def node44Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,6,7,8,9,3,2,5,4,15,14,0,1,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,7,6,9,8,2,3,4,5,14,15,1,0,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node44Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,12,13,10,11,15,14,1,0,2,3,5,4,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,0,1,15,14,4,5,2,3,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node44Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,13,12,10,11,1,0,15,14,4,5,3,2,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,13,12,10,11,1,0,15,14,4,5,3,2,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node44Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node44Generator0 else (if j.val < 2 then node44Generator1 else node44Generator2))

def node45Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,15,14,10,11,13,12,7,6,8,9,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,14,15,11,10,12,13,6,7,9,8,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node45Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,7,6,5,4,2,3,0,1,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,7,6,5,4,2,3,0,1,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node45Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node45Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node45Generator0 else (if j.val < 2 then node45Generator1 else node45Generator2))

def node46Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,9,8,7,6,12,13,10,11,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,9,8,7,6,12,13,10,11,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node46Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,0,1,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,15,14,0,1,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node46Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node46Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,2,3,7,6,9,8,10,11,12,13,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,4,5,2,3,7,6,9,8,10,11,12,13,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node46Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node46Generator0 else node46Generator1) else (if j.val < 3 then node46Generator2 else node46Generator3))

def node47Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,14,15,4,5,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,14,15,4,5,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node47Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,0,1,2,3,4,5,15,14,8,9,10,11,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,4,5,6,7,1,0,10,11,12,13,14,15,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node47Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,11,10,0,1,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,10,11,1,0,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node47Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node47Generator0 else (if j.val < 2 then node47Generator1 else node47Generator2))

def node48Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,5,4,10,11,1,0,6,7,13,12,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,5,4,10,11,1,0,6,7,13,12,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node48Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,0,1,3,2,5,4,6,7,9,8,10,11,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,5,4,7,6,8,9,11,10,12,13,14,15,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node48Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,8,9,14,15,5,4,11,10,1,0,7,6,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,0,1,7,6,13,12,2,3,9,8,14,15,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node48Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node48Generator0 else (if j.val < 2 then node48Generator1 else node48Generator2))

def node49Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,6,7,0,1,11,10,12,13,14,15,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,1,0,2,3,4,5,14,15,9,8,10,11,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node49Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,15,14,13,12,6,7,5,4,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,11,10,8,9,3,2,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node49Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node49Generator0 else node49Generator1)

def node50Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node50Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node50Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,14,15,9,8,7,6,2,3,0,1,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,14,15,9,8,7,6,2,3,0,1,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node50Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node50Generator0 else (if j.val < 2 then node50Generator1 else node50Generator2))

def node51Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,6,7,3,2,5,4,15,14,0,1,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,7,6,9,8,4,5,2,3,1,0,14,15,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node51Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,13,12,11,10,14,15,1,0,3,2,5,4,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,13,12,1,0,14,15,5,4,3,2,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node51Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,13,12,11,10,0,1,15,14,5,4,3,2,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,13,12,11,10,0,1,15,14,5,4,3,2,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node51Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node51Generator0 else (if j.val < 2 then node51Generator1 else node51Generator2))

def node52Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,11,10,12,13,7,6,8,9,3,2,4,5,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,11,10,12,13,7,6,8,9,3,2,4,5,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node52Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,15,14,8,9,11,10,12,13,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,1,0,2,3,13,12,6,7,9,8,10,11,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node52Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node52Generator0 else node52Generator1)

def node53Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,10,11,12,13,7,6,9,8,2,3,4,5,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,10,11,12,13,7,6,9,8,2,3,4,5,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node53Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,5,4,14,15,8,9,11,10,13,12,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,1,0,3,2,12,13,6,7,9,8,11,10,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node53Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node53Generator0 else node53Generator1)

def node54Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node54Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,13,12,10,11,1,0,15,14,5,4,2,3,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,12,13,11,10,0,1,14,15,4,5,3,2,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node54Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,3,2,0,1,7,6,4,5,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,10,11,9,8,15,14,13,12,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node54Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node54Generator0 else (if j.val < 2 then node54Generator1 else node54Generator2))

def node55Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,11,10,8,9,7,6,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,10,11,9,8,6,7,5,4,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node55Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,0,1,2,3,4,5,7,6,8,9,11,10,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,4,5,6,7,9,8,10,11,13,12,14,15,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node55Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node55Generator0 else node55Generator1)

def node56Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,0,1,2,3,5,4,7,6,9,8,11,10,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,4,5,7,6,9,8,11,10,13,12,15,14,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node56Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node56Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node56Generator0 else node56Generator1)

def node67Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node67Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node67Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node67Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node67Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,13,12,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,14,15,13,12,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node67Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node67Generator0 else node67Generator1) else (if j.val < 3 then node67Generator2 else (if j.val < 4 then node67Generator3 else node67Generator4)))

def node68Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,9,8,7,6,13,12,11,10,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,9,8,7,6,13,12,11,10,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node68Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,15,14,0,1,11,10,13,12,6,7,8,9,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,14,15,1,0,10,11,12,13,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node68Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,14,15,0,1,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,15,14,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node68Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,2,3,4,5,9,8,7,6,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,2,3,4,5,9,8,7,6,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node68Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,4,5,2,3,6,7,8,9,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,4,5,2,3,6,7,8,9,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node68Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node68Generator0 else node68Generator1) else (if j.val < 3 then node68Generator2 else (if j.val < 4 then node68Generator3 else node68Generator4)))

def node69Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,9,8,7,6,13,12,11,10,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,9,8,7,6,13,12,11,10,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node69Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node69Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,0,1,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,15,14,0,1,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node69Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,13,12,14,15,0,1,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,13,12,14,15,0,1,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node69Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,2,3,4,5,9,8,7,6,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,2,3,4,5,9,8,7,6,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node69Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,4,5,2,3,6,7,8,9,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,4,5,2,3,6,7,8,9,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node69Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node69Generator0 else (if j.val < 2 then node69Generator1 else node69Generator2)) else (if j.val < 4 then node69Generator3 else (if j.val < 5 then node69Generator4 else node69Generator5)))

def node70Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node70Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node70Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,3,2,1,0,14,15,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,1,0,2,3,13,12,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node70Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,13,12,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,14,15,13,12,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node70Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node70Generator0 else node70Generator1) else (if j.val < 3 then node70Generator2 else node70Generator3))

def node71Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,10,11,9,8,5,4,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,9,8,11,10,7,6,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node71Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node71Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,2,3,0,1,14,15,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,0,1,3,2,12,13,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node71Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node71Generator0 else (if j.val < 2 then node71Generator1 else node71Generator2))

def node72Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,13,12,15,14,0,1,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,13,12,15,14,0,1,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node72Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,7,6,9,8,3,2,5,4,14,15,0,1,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,7,6,9,8,3,2,5,4,14,15,0,1,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node72Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,5,4,7,6,0,1,2,3,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,7,6,9,8,2,3,5,4,15,14,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node72Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node72Generator0 else (if j.val < 2 then node72Generator1 else node72Generator2))

def node73Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,9,8,7,6,12,13,10,11,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,9,8,7,6,12,13,10,11,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node73Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,0,1,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,15,14,0,1,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node73Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,14,15,0,1,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,15,14,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node73Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,3,2,5,4,8,9,6,7,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,3,2,5,4,8,9,6,7,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node73Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node73Generator0 else node73Generator1) else (if j.val < 3 then node73Generator2 else node73Generator3))

def node74Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node74Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,9,8,0,1,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,10,11,7,6,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node74Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node74Generator0 else node74Generator1)

end SymmetricSubgroupAsymptotics.BinaryActionData16
