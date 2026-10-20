import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
96 through 127. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node107Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,9,8,1,0,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,11,10,7,6,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node107Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,14,15,2,3,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,12,13,5,4,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node107Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,12,13,2,3,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,13,12,3,2,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node107Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node107Generator0 else (if j.val < 2 then node107Generator1 else node107Generator2))

def node108Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,8,9,10,11,6,7,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,11,10,8,9,4,5,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node108Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,14,15,12,13,3,2,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,13,12,14,15,0,1,2,3,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node108Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node108Generator0 else node108Generator1)

def node109Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,9,8,7,6,13,12,11,10,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,9,8,7,6,13,12,11,10,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node109Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,0,1,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,15,14,0,1,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node109Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,14,15,0,1,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,15,14,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node109Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,3,2,5,4,8,9,6,7,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,3,2,5,4,8,9,6,7,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node109Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,4,5,2,3,6,7,8,9,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,4,5,2,3,6,7,8,9,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node109Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node109Generator0 else node109Generator1) else (if j.val < 3 then node109Generator2 else (if j.val < 4 then node109Generator3 else node109Generator4)))

def node110Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,10,11,2,3,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,12,13,0,1,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node110Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,9,8,1,0,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,11,10,7,6,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node110Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node110Generator0 else node110Generator1)

def node111Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,14,15,6,7,8,9,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,1,0,2,3,6,7,8,9,10,11,12,13,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node111Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,7,6,15,14,0,1,3,2,4,5,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,5,4,15,14,0,1,2,3,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node111Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,2,3,4,5,14,15,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,6,7,8,9,14,15,1,0,2,3,5,4,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node111Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node111Generator0 else (if j.val < 2 then node111Generator1 else node111Generator2))

def node112Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,11,10,9,8,12,13,14,15,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,2,3,1,0,7,6,5,4,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node112Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,13,12,14,15,2,3,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,13,12,14,15,2,3,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node112Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,13,12,14,15,3,2,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,12,13,15,14,2,3,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node112Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node112Generator0 else (if j.val < 2 then node112Generator1 else node112Generator2))

def node113Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,14,15,4,5,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,8,9,11,10,0,1,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node113Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,1,0,2,3,4,5,14,15,9,8,10,11,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,4,5,6,7,0,1,11,10,12,13,14,15,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node113Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node113Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node113Generator0 else (if j.val < 2 then node113Generator1 else node113Generator2))

def node114Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,13,12,2,3,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,13,12,2,3,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node114Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,8,9,10,11,4,5,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,10,11,4,5,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node114Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,14,15,4,5,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,10,11,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node114Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node114Generator0 else (if j.val < 2 then node114Generator1 else node114Generator2))

def node115Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,9,8,7,6,12,13,10,11,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,9,8,7,6,12,13,10,11,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node115Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,0,1,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,15,14,0,1,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node115Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,14,15,0,1,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,15,14,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node115Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,2,3,4,5,9,8,7,6,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,2,3,4,5,9,8,7,6,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node115Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node115Generator0 else node115Generator1) else (if j.val < 3 then node115Generator2 else node115Generator3))

def node116Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node116Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node116Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,1,0,6,7,2,3,12,13,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,6,7,0,1,4,5,14,15,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node116Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,15,14,4,5,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,14,15,5,4,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node116Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node116Generator0 else node116Generator1) else (if j.val < 3 then node116Generator2 else node116Generator3))

def node117Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node117Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node117Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node117Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,12,13,3,2,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,12,13,3,2,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node117Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node117Generator0 else node117Generator1) else (if j.val < 3 then node117Generator2 else node117Generator3))

def node118Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node118Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node118Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node118Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,12,13,2,3,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,12,13,2,3,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node118Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node118Generator0 else node118Generator1) else (if j.val < 3 then node118Generator2 else node118Generator3))

def node119Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,9,8,7,6,13,12,11,10,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,9,8,7,6,13,12,11,10,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node119Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,0,1,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,15,14,0,1,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node119Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,14,15,0,1,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,15,14,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node119Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,2,3,4,5,9,8,7,6,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,2,3,4,5,9,8,7,6,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node119Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,4,5,2,3,6,7,8,9,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,4,5,2,3,6,7,8,9,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node119Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node119Generator0 else node119Generator1) else (if j.val < 3 then node119Generator2 else (if j.val < 4 then node119Generator3 else node119Generator4)))

def node120Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node120Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node120Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,12,13,2,3,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,12,13,2,3,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node120Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node120Generator0 else (if j.val < 2 then node120Generator1 else node120Generator2))

def node121Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,13,12,7,6,8,9,10,11,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,9,8,10,11,12,13,7,6,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node121Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,7,6,2,3,4,5,15,14,1,0,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,6,7,8,9,5,4,15,14,1,0,3,2,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node121Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node121Generator0 else node121Generator1)

def node122Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node122Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node122Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,10,11,6,7,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,8,9,0,1,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node122Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node122Generator0 else (if j.val < 2 then node122Generator1 else node122Generator2))

def node123Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,12,13,14,15,2,3,0,1,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,13,12,15,14,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node123Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node123Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node123Generator0 else node123Generator1)

def node124Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node124Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node124Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node124Generator0 else node124Generator1)

def node125Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,5,4,6,7,1,0,14,15,9,8,11,10,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,1,0,3,2,4,5,11,10,13,12,15,14,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node125Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,15,14,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,12,13,1,0,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node125Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node125Generator0 else node125Generator1)

def node126Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,3,2,9,8,14,15,5,4,11,10,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,3,2,9,8,14,15,5,4,11,10,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node126Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,3,2,12,13,6,7,1,0,10,11,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,5,4,15,14,8,9,3,2,12,13,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node126Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,6,7,4,5,2,3,1,0,14,15,12,13,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,6,7,4,5,2,3,1,0,14,15,12,13,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node126Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node126Generator0 else (if j.val < 2 then node126Generator1 else node126Generator2))

def node127Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,14,15,9,8,11,10,13,12,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,14,15,9,8,11,10,13,12,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node127Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,0,1,11,10,12,13,7,6,8,9,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,15,14,0,1,11,10,12,13,7,6,8,9,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node127Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,4,5,2,3,9,8,7,6,12,13,10,11,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,4,5,2,3,9,8,7,6,12,13,10,11,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node127Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node127Generator0 else (if j.val < 2 then node127Generator1 else node127Generator2))

def node128Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,14,15,9,8,10,11,13,12,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,14,15,9,8,10,11,13,12,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node128Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,14,15,0,1,10,11,12,13,6,7,8,9,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,14,15,0,1,10,11,12,13,6,7,8,9,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node128Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,5,4,3,2,9,8,7,6,13,12,11,10,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,5,4,3,2,9,8,7,6,13,12,11,10,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node128Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node128Generator0 else (if j.val < 2 then node128Generator1 else node128Generator2))

def node129Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,15,14,0,1,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,15,14,0,1,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node129Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,15,14,6,7,13,12,10,11,9,8,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,1,0,2,3,6,7,13,12,10,11,9,8,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node129Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,8,9,10,11,5,4,15,14,1,0,3,2,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,7,6,0,1,2,3,4,5,14,15,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node129Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node129Generator0 else (if j.val < 2 then node129Generator1 else node129Generator2))

def node130Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,14,15,9,8,10,11,13,12,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,14,15,9,8,10,11,13,12,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node130Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,5,4,15,14,9,8,11,10,13,12,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,1,0,3,2,13,12,7,6,9,8,11,10,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node130Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node130Generator0 else node130Generator1)

def node131Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,12,13,4,5,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,14,15,2,3,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node131Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node131Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node131Generator0 else node131Generator1)

def node132Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,11,10,9,8,2,3,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,14,15,12,13,7,6,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node132Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,3,2,1,0,6,7,13,12,10,11,9,8,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,3,2,1,0,6,7,13,12,10,11,9,8,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node132Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node132Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node132Generator0 else (if j.val < 2 then node132Generator1 else node132Generator2))

def node133Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,14,15,5,4,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,9,8,11,10,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node133Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,5,4,7,6,0,1,10,11,13,12,14,15,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,1,0,3,2,5,4,14,15,8,9,11,10,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node133Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,11,10,9,8,3,2,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,15,14,13,12,7,6,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node133Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node133Generator0 else (if j.val < 2 then node133Generator1 else node133Generator2))

def node134Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,10,11,9,8,7,6,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,10,11,9,8,7,6,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node134Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,0,1,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,0,1,7,6,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node134Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,10,11,9,8,6,7,5,4,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,11,10,8,9,7,6,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node134Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node134Generator0 else (if j.val < 2 then node134Generator1 else node134Generator2))

def node135Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,9,8,7,6,12,13,10,11,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,9,8,7,6,12,13,10,11,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node135Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,6,7,3,2,5,4,14,15,1,0,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,7,6,9,8,4,5,2,3,0,1,15,14,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node135Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,7,6,15,14,1,0,2,3,5,4,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,5,4,2,3,0,1,14,15,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node135Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node135Generator0 else (if j.val < 2 then node135Generator1 else node135Generator2))

def node136Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,11,10,9,8,3,2,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,13,12,7,6,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node136Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,0,1,6,7,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,0,1,6,7,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node136Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node136Generator0 else node136Generator1)

def node137Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node137Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node137Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,12,13,2,3,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,12,13,2,3,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node137Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node137Generator0 else (if j.val < 2 then node137Generator1 else node137Generator2))

def node138Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,8,9,1,0,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,11,10,6,7,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node138Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,10,11,1,0,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,11,10,0,1,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node138Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node138Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node138Generator0 else (if j.val < 2 then node138Generator1 else node138Generator2))

end SymmetricSubgroupAsymptotics.BinaryActionData16
