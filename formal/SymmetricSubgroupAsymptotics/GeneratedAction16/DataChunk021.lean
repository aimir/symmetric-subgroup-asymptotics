import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
672 through 703. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node806Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node806Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node806Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node806Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node806Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,9,8,10,11,4,5,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,8,9,11,10,5,4,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node806Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,10,11,9,8,6,7,5,4,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,11,10,8,9,7,6,4,5,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node806Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node806Generator0 else (if j.val < 2 then node806Generator1 else node806Generator2)) else (if j.val < 4 then node806Generator3 else (if j.val < 5 then node806Generator4 else node806Generator5)))

def node807Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node807Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node807Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,2,3,1,0,15,14,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,1,0,2,3,13,12,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node807Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,13,12,15,14,0,1,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,14,15,12,13,2,3,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node807Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,13,12,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node807Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node807Generator0 else node807Generator1) else (if j.val < 3 then node807Generator2 else (if j.val < 4 then node807Generator3 else node807Generator4)))

def node808Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node808Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node808Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node808Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node808Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node808Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node808Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node808Generator0 else (if j.val < 2 then node808Generator1 else node808Generator2)) else (if j.val < 4 then node808Generator3 else (if j.val < 5 then node808Generator4 else node808Generator5)))

def node809Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node809Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node809Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node809Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node809Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node809Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node809Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node809Generator0 else (if j.val < 2 then node809Generator1 else node809Generator2)) else (if j.val < 4 then node809Generator3 else (if j.val < 5 then node809Generator4 else node809Generator5)))

def node810Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node810Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node810Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,2,3,0,1,13,12,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,0,1,2,3,14,15,12,13,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node810Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,0,1,13,12,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,0,1,12,13,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node810Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node810Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node810Generator0 else node810Generator1) else (if j.val < 3 then node810Generator2 else (if j.val < 4 then node810Generator3 else node810Generator4)))

def node811Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,0,1,2,3,7,6,5,4,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,11,10,9,8,15,14,13,12,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node811Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,5,4,7,6,10,11,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,5,4,7,6,11,10,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node811Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node811Generator0 else node811Generator1)

def node812Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,10,11,9,8,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,11,10,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node812Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,11,10,9,8,6,7,5,4,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,11,10,8,9,7,6,5,4,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node812Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,13,12,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,14,15,3,2,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node812Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node812Generator0 else (if j.val < 2 then node812Generator1 else node812Generator2))

def node813Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,3,2,14,15,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,2,3,15,14,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node813Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,14,15,13,12,1,0,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,14,15,12,13,1,0,2,3,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node813Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,5,4,7,6,8,9,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,5,4,7,6,8,9,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node813Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node813Generator0 else (if j.val < 2 then node813Generator1 else node813Generator2))

def node814Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,3,2,14,15,13,12,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,3,2,13,12,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node814Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,9,8,10,11,5,4,6,7,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,9,8,10,11,5,4,6,7,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node814Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,7,6,10,11,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,7,6,10,11,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node814Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node814Generator0 else (if j.val < 2 then node814Generator1 else node814Generator2))

def node815Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node815Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node815Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,1,0,2,3,5,4,14,15,9,8,10,11,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,4,5,7,6,0,1,11,10,12,13,15,14,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node815Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node815Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node815Generator0 else node815Generator1) else (if j.val < 3 then node815Generator2 else node815Generator3))

def node816Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,11,10,9,8,7,6,5,4,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,11,10,9,8,7,6,5,4,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node816Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,14,15,13,12,3,2,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,12,13,0,1,2,3,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node816Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,2,3,1,0,15,14,13,12,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,13,12,15,14,0,1,3,2,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node816Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node816Generator0 else (if j.val < 2 then node816Generator1 else node816Generator2))

def node817Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,14,15,2,3,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,12,13,1,0,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node817Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,14,15,2,3,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,12,13,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node817Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node817Generator0 else node817Generator1)

def node818Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node818Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node818Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node818Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node818Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,12,13,0,1,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,15,14,13,12,0,1,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node818Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node818Generator0 else node818Generator1) else (if j.val < 3 then node818Generator2 else (if j.val < 4 then node818Generator3 else node818Generator4)))

def node819Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node819Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node819Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node819Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node819Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,12,13,0,1,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,15,14,13,12,0,1,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node819Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node819Generator0 else node819Generator1) else (if j.val < 3 then node819Generator2 else (if j.val < 4 then node819Generator3 else node819Generator4)))

def node820Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node820Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,9,8,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node820Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,0,1,3,2,5,4,15,14,9,8,11,10,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,5,4,7,6,1,0,11,10,13,12,14,15,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node820Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node820Generator0 else (if j.val < 2 then node820Generator1 else node820Generator2))

def node821Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,14,15,2,3,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,14,15,13,12,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node821Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,8,9,11,10,5,4,7,6,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,9,8,11,10,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node821Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,0,1,2,3,14,15,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,2,3,1,0,13,12,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node821Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node821Generator0 else (if j.val < 2 then node821Generator1 else node821Generator2))

def node822Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,11,10,8,9,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,10,11,9,8,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node822Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,9,8,10,11,4,5,7,6,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,8,9,11,10,5,4,6,7,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node822Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,12,13,15,14,3,2,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,13,12,14,15,3,2,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node822Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node822Generator0 else (if j.val < 2 then node822Generator1 else node822Generator2))

def node823Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,9,8,10,11,4,5,7,6,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,8,9,11,10,5,4,6,7,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node823Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,0,1,2,3,11,10,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,2,3,1,0,10,11,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node823Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,12,13,14,15,3,2,0,1,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,13,12,15,14,3,2,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node823Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node823Generator0 else (if j.val < 2 then node823Generator1 else node823Generator2))

def node824Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,11,10,9,8,5,4,7,6,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,9,8,11,10,7,6,5,4,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node824Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,13,12,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,14,15,12,13,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node824Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,15,14,6,7,5,4,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,11,10,8,9,1,0,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node824Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node824Generator0 else (if j.val < 2 then node824Generator1 else node824Generator2))

def node825Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,11,10,9,8,4,5,6,7,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,8,9,10,11,7,6,5,4,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node825Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,3,2,13,12,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,2,3,13,12,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node825Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,13,12,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,14,15,3,2,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node825Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node825Generator0 else (if j.val < 2 then node825Generator1 else node825Generator2))

def node826Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,10,11,9,8,12,13,14,15,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,2,3,0,1,7,6,4,5,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node826Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,14,15,3,2,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,13,12,0,1,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node826Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,15,14,13,12,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,12,13,14,15,1,0,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node826Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node826Generator0 else (if j.val < 2 then node826Generator1 else node826Generator2))

def node827Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node827Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node827Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node827Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node827Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,12,13,0,1,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,15,14,13,12,0,1,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node827Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node827Generator0 else node827Generator1) else (if j.val < 3 then node827Generator2 else (if j.val < 4 then node827Generator3 else node827Generator4)))

def node828Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,2,3,0,1,5,4,7,6,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,9,8,11,10,13,12,14,15,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node828Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,2,3,0,1,7,6,5,4,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,11,10,9,8,13,12,15,14,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node828Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node828Generator0 else node828Generator1)

def node829Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,1,0,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,10,11,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node829Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node829Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,15,14,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,4,5,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node829Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node829Generator0 else (if j.val < 2 then node829Generator1 else node829Generator2))

def node830Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,9,8,10,11,4,5,7,6,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,8,9,11,10,5,4,6,7,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node830Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,14,15,13,12,3,2,1,0,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,1,0,3,2,12,13,15,14,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node830Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,8,9,11,10,7,6,4,5,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,10,11,9,8,4,5,7,6,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node830Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node830Generator0 else (if j.val < 2 then node830Generator1 else node830Generator2))

def node831Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,0,1,2,3,12,13,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,2,3,1,0,15,14,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node831Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,11,10,8,9,12,13,14,15,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,0,1,3,2,6,7,5,4,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node831Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,5,4,7,6,10,11,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,5,4,7,6,11,10,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node831Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node831Generator0 else (if j.val < 2 then node831Generator1 else node831Generator2))

def node832Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,11,10,8,9,14,15,12,13,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,1,0,2,3,6,7,5,4,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node832Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,11,10,8,9,12,13,15,14,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,2,3,1,0,6,7,5,4,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node832Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node832Generator0 else node832Generator1)

def node833Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,4,5,6,7,9,8,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,4,5,6,7,9,8,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node833Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,1,0,3,2,13,12,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,2,3,0,1,14,15,13,12,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node833Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,9,8,11,10,7,6,4,5,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,10,11,9,8,5,4,7,6,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node833Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node833Generator0 else (if j.val < 2 then node833Generator1 else node833Generator2))

def node834Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,14,15,8,9,7,6,2,3,0,1,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,14,15,9,8,6,7,3,2,0,1,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node834Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,1,0,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,1,0,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node834Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,0,1,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,1,0,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node834Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node834Generator0 else (if j.val < 2 then node834Generator1 else node834Generator2))

def node835Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,0,1,10,11,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,1,0,10,11,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node835Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,14,15,9,8,7,6,2,3,0,1,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,14,15,9,8,7,6,3,2,1,0,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node835Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,10,11,12,13,2,3,7,6,5,4,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,13,12,11,10,0,1,4,5,6,7,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node835Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node835Generator0 else (if j.val < 2 then node835Generator1 else node835Generator2))

def node836Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,0,1,3,2,7,6,5,4,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,11,10,9,8,14,15,13,12,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node836Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,2,3,1,0,6,7,5,4,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,11,10,8,9,12,13,15,14,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node836Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node836Generator0 else node836Generator1)

def node837Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node837Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node837Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node837Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node837Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,12,13,0,1,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,15,14,13,12,0,1,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node837Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node837Generator0 else node837Generator1) else (if j.val < 3 then node837Generator2 else (if j.val < 4 then node837Generator3 else node837Generator4)))

end SymmetricSubgroupAsymptotics.BinaryActionData16
