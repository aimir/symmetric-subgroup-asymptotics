import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
704 through 735. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node838Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node838Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node838Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node838Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,12,13,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,12,13,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node838Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,4,5,6,7,3,2,0,1,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,4,5,6,7,2,3,1,0,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node838Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node838Generator0 else node838Generator1) else (if j.val < 3 then node838Generator2 else (if j.val < 4 then node838Generator3 else node838Generator4)))

def node839Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node839Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node839Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node839Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node839Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,12,13,0,1,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,15,14,13,12,0,1,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node839Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node839Generator0 else node839Generator1) else (if j.val < 3 then node839Generator2 else (if j.val < 4 then node839Generator3 else node839Generator4)))

def node840Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,8,9,11,10,12,13,14,15,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,3,2,1,0,4,5,7,6,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node840Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,14,15,13,12,2,3,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,15,14,13,12,2,3,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node840Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node840Generator0 else node840Generator1)

def node841Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,8,9,11,10,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node841Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,8,9,4,5,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,8,9,10,11,6,7,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node841Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node841Generator0 else node841Generator1)

def node842Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,8,9,11,10,6,7,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,11,10,8,9,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node842Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,1,0,2,3,8,9,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,2,3,1,0,8,9,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node842Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,13,12,15,14,7,6,4,5,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,10,11,9,8,3,2,0,1,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node842Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node842Generator0 else (if j.val < 2 then node842Generator1 else node842Generator2))

def node843Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node843Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,11,10,8,9,7,6,4,5,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,10,11,9,8,6,7,5,4,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node843Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,2,3,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,14,15,12,13,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node843Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,15,14,13,12,2,3,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,12,13,14,15,0,1,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node843Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node843Generator0 else node843Generator1) else (if j.val < 3 then node843Generator2 else node843Generator3))

def node844Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,13,12,15,14,7,6,5,4,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,11,10,9,8,2,3,0,1,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node844Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,3,2,1,0,14,15,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,1,0,2,3,13,12,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node844Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,3,2,1,0,15,14,12,13,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,1,0,2,3,13,12,15,14,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node844Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node844Generator0 else (if j.val < 2 then node844Generator1 else node844Generator2))

def node845Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,13,12,14,15,3,2,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,13,12,14,15,2,3,1,0,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node845Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,1,0,3,2,6,7,5,4,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,11,10,8,9,13,12,14,15,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node845Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,6,7,5,4,3,2,0,1,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,7,6,4,5,0,1,2,3,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node845Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node845Generator0 else (if j.val < 2 then node845Generator1 else node845Generator2))

def node846Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,9,8,10,11,7,6,5,4,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,11,10,9,8,5,4,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node846Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,3,2,1,0,14,15,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,1,0,2,3,13,12,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node846Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,9,8,11,10,6,7,5,4,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,11,10,8,9,5,4,7,6,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node846Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node846Generator0 else (if j.val < 2 then node846Generator1 else node846Generator2))

def node847Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,9,8,10,11,7,6,4,5,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,10,11,9,8,5,4,6,7,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node847Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,7,6,4,5,9,8,10,11,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,6,7,5,4,9,8,10,11,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node847Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,14,15,13,12,2,3,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,15,14,12,13,3,2,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node847Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node847Generator0 else (if j.val < 2 then node847Generator1 else node847Generator2))

def node848Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,11,10,8,9,5,4,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,9,8,10,11,6,7,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node848Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,5,4,6,7,8,9,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,5,4,6,7,8,9,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node848Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,14,15,12,13,0,1,2,3,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,15,14,13,12,0,1,2,3,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node848Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node848Generator0 else (if j.val < 2 then node848Generator1 else node848Generator2))

def node849Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,10,11,8,9,14,15,13,12,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,0,1,3,2,6,7,4,5,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node849Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node849Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,14,15,12,13,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,15,14,2,3,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node849Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node849Generator0 else (if j.val < 2 then node849Generator1 else node849Generator2))

def node850Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node850Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node850Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node850Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,3,2,0,1,12,13,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,0,1,2,3,14,15,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node850Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node850Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node850Generator0 else node850Generator1) else (if j.val < 3 then node850Generator2 else (if j.val < 4 then node850Generator3 else node850Generator4)))

def node851Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,2,3,0,1,13,12,15,14,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,1,0,2,3,15,14,12,13,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node851Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,0,1,2,3,12,13,15,14,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,13,12,15,14,1,0,2,3,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node851Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,11,10,9,8,6,7,4,5,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,10,11,8,9,7,6,5,4,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node851Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node851Generator0 else (if j.val < 2 then node851Generator1 else node851Generator2))

def node852Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,9,8,10,11,1,0,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,15,14,5,4,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node852Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,14,15,12,13,6,7,5,4,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,11,10,8,9,0,1,2,3,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node852Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,10,11,9,8,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,15,14,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node852Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node852Generator0 else (if j.val < 2 then node852Generator1 else node852Generator2))

def node853Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,1,0,14,15,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,1,0,15,14,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node853Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,14,15,12,13,0,1,2,3,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,14,15,12,13,0,1,2,3,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node853Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,0,1,3,2,13,12,15,14,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,3,2,1,0,15,14,12,13,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node853Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node853Generator0 else (if j.val < 2 then node853Generator1 else node853Generator2))

def node854Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,1,0,11,10,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,1,0,11,10,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node854Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,11,10,2,3,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,13,12,0,1,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node854Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,8,9,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node854Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node854Generator0 else (if j.val < 2 then node854Generator1 else node854Generator2))

def node855Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,11,10,9,8,4,5,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,8,9,10,11,7,6,5,4,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node855Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node855Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,12,13,15,14,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,15,14,2,3,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node855Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node855Generator0 else (if j.val < 2 then node855Generator1 else node855Generator2))

def node856Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,14,15,3,2,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,13,12,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node856Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,11,10,9,8,5,4,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,9,8,11,10,7,6,5,4,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node856Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,8,9,10,11,6,7,4,5,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,10,11,8,9,4,5,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node856Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node856Generator0 else (if j.val < 2 then node856Generator1 else node856Generator2))

def node857Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,9,8,11,10,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,12,13,14,15,5,4,7,6,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node857Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,12,13,14,15,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node857Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,0,1,2,3,8,9,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,3,2,0,1,8,9,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node857Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node857Generator0 else (if j.val < 2 then node857Generator1 else node857Generator2))

def node858Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,1,0,2,3,6,7,5,4,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,11,10,8,9,12,13,15,14,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node858Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,2,3,0,1,5,4,6,7,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,9,8,10,11,14,15,12,13,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node858Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,6,7,4,5,10,11,8,9,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,6,7,4,5,10,11,8,9,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node858Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node858Generator0 else (if j.val < 2 then node858Generator1 else node858Generator2))

def node859Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,9,8,11,10,14,15,12,13,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,2,3,0,1,5,4,7,6,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node859Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,4,5,11,10,8,9,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,4,5,10,11,9,8,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node859Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,10,11,9,8,13,12,14,15,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,0,1,3,2,7,6,4,5,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node859Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node859Generator0 else (if j.val < 2 then node859Generator1 else node859Generator2))

def node860Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node860Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node860Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node860Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,10,11,13,12,3,2,6,7,5,4,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,13,12,10,11,1,0,4,5,7,6,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node860Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node860Generator0 else node860Generator1) else (if j.val < 3 then node860Generator2 else node860Generator3))

def node861Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node861Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node861Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node861Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,4,5,6,7,3,2,0,1,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,4,5,6,7,2,3,1,0,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node861Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,14,15,13,12,2,3,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,14,15,13,12,3,2,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node861Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node861Generator0 else node861Generator1) else (if j.val < 3 then node861Generator2 else (if j.val < 4 then node861Generator3 else node861Generator4)))

def node862Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,11,10,8,9,6,7,4,5,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,10,11,8,9,6,7,5,4,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node862Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,15,14,3,2,0,1,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,13,12,15,14,1,0,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node862Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,8,9,10,11,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,10,11,9,8,4,5,6,7,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node862Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node862Generator0 else (if j.val < 2 then node862Generator1 else node862Generator2))

def node863Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node863Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,2,3,0,1,14,15,12,13,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,0,1,2,3,12,13,14,15,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node863Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,9,8,11,10,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,13,12,15,14,5,4,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node863Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node863Generator0 else (if j.val < 2 then node863Generator1 else node863Generator2))

def node864Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,12,13,6,7,5,4,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,11,10,8,9,2,3,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node864Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,2,3,0,1,13,12,14,15,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,1,0,2,3,14,15,12,13,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node864Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,5,4,7,6,11,10,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,5,4,7,6,10,11,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node864Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node864Generator0 else (if j.val < 2 then node864Generator1 else node864Generator2))

def node865Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,12,13,14,15,3,2,0,1,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,0,1,3,2,14,15,12,13,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node865Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,9,8,10,11,6,7,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,11,10,8,9,5,4,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node865Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,14,15,13,12,3,2,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,13,12,2,3,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node865Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node865Generator0 else (if j.val < 2 then node865Generator1 else node865Generator2))

def node866Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node866Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,8,9,11,10,4,5,7,6,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,8,9,11,10,4,5,7,6,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node866Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,5,4,6,7,10,11,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,5,4,6,7,10,11,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node866Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,13,12,15,14,0,1,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,15,14,12,13,3,2,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node866Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node866Generator0 else node866Generator1) else (if j.val < 3 then node866Generator2 else node866Generator3))

def node867Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,1,0,2,3,14,15,12,13,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,12,13,14,15,2,3,1,0,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node867Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,11,10,8,9,4,5,7,6,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,8,9,11,10,6,7,5,4,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node867Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,11,10,9,8,5,4,7,6,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,9,8,11,10,7,6,5,4,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node867Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node867Generator0 else (if j.val < 2 then node867Generator1 else node867Generator2))

def node868Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node868Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node868Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node868Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node868Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,12,13,0,1,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,15,14,13,12,0,1,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node868Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node868Generator0 else node868Generator1) else (if j.val < 3 then node868Generator2 else (if j.val < 4 then node868Generator3 else node868Generator4)))

def node869Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,10,11,8,9,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,10,11,9,8,6,7,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node869Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,6,7,4,5,10,11,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,6,7,4,5,10,11,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node869Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,2,3,15,14,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,2,3,14,15,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node869Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node869Generator0 else (if j.val < 2 then node869Generator1 else node869Generator2))

end SymmetricSubgroupAsymptotics.BinaryActionData16
