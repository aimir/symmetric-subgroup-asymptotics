import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
352 through 383. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node382Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,15,14,7,6,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,9,8,5,4,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node382Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node382Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,12,13,4,5,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,14,15,3,2,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node382Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node382Generator0 else (if j.val < 2 then node382Generator1 else node382Generator2))

def node383Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,9,8,10,11,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,10,11,9,8,5,4,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node383Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,2,3,1,0,15,14,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,0,1,3,2,12,13,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node383Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,10,11,8,9,4,5,6,7,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,8,9,10,11,6,7,4,5,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node383Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node383Generator0 else (if j.val < 2 then node383Generator1 else node383Generator2))

def node384Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,11,10,9,8,4,5,6,7,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,8,9,10,11,7,6,5,4,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node384Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,15,14,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,15,14,13,12,1,0,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node384Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,15,14,12,13,0,1,2,3,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,15,14,12,13,1,0,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node384Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node384Generator0 else (if j.val < 2 then node384Generator1 else node384Generator2))

def node385Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,9,8,11,10,13,12,15,14,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,3,2,1,0,5,4,7,6,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node385Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node385Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,7,6,5,4,0,1,2,3,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,7,6,5,4,1,0,3,2,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node385Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node385Generator0 else (if j.val < 2 then node385Generator1 else node385Generator2))

def node386Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node386Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,8,9,6,7,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,8,9,6,7,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node386Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,14,15,7,6,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,9,8,4,5,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node386Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node386Generator0 else (if j.val < 2 then node386Generator1 else node386Generator2))

def node387Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,5,4,6,7,0,1,12,13,11,10,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,0,1,3,2,4,5,12,13,11,10,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node387Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,14,15,12,13,4,5,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,10,11,3,2,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node387Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node387Generator0 else node387Generator1)

def node388Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,14,15,8,9,11,10,12,13,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,14,15,8,9,11,10,12,13,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node388Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,5,4,14,15,8,9,11,10,13,12,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,1,0,3,2,12,13,6,7,9,8,11,10,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node388Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,0,1,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,0,1,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node388Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node388Generator0 else (if j.val < 2 then node388Generator1 else node388Generator2))

def node389Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,7,6,5,4,3,2,1,0,15,14,13,12,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,7,6,5,4,3,2,1,0,15,14,13,12,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node389Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,13,12,11,10,1,0,15,14,5,4,3,2,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,13,12,11,10,1,0,15,14,5,4,3,2,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node389Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,7,6,4,5,10,11,9,8,15,14,12,13,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,14,15,4,5,3,2,9,8,6,7,12,13,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node389Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node389Generator0 else (if j.val < 2 then node389Generator1 else node389Generator2))

def node390Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,14,15,9,8,10,11,13,12,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,14,15,9,8,10,11,13,12,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node390Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,5,4,15,14,9,8,11,10,13,12,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,1,0,3,2,13,12,7,6,9,8,11,10,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node390Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,0,1,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,0,1,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node390Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node390Generator0 else (if j.val < 2 then node390Generator1 else node390Generator2))

def node391Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,14,15,9,8,10,11,13,12,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,14,15,9,8,10,11,13,12,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node391Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,5,4,14,15,9,8,10,11,13,12,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,0,1,3,2,12,13,7,6,8,9,11,10,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node391Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,0,1,7,6,12,13,11,10,8,9,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,0,1,7,6,12,13,11,10,8,9,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node391Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node391Generator0 else (if j.val < 2 then node391Generator1 else node391Generator2))

def node392Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,15,14,6,7,12,13,10,11,8,9,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,1,0,2,3,6,7,12,13,10,11,8,9,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node392Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,14,15,5,4,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,15,14,4,5,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node392Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,15,14,1,0,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,12,13,15,14,1,0,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node392Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node392Generator0 else (if j.val < 2 then node392Generator1 else node392Generator2))

def node393Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,14,15,9,8,11,10,13,12,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,14,15,9,8,11,10,13,12,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node393Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,14,15,9,8,11,10,12,13,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,1,0,2,3,12,13,7,6,9,8,10,11,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node393Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,0,1,7,6,12,13,11,10,8,9,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,0,1,7,6,12,13,11,10,8,9,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node393Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node393Generator0 else (if j.val < 2 then node393Generator1 else node393Generator2))

def node394Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,12,13,14,15,7,6,5,4,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,11,10,9,8,3,2,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node394Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node394Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,12,13,15,14,7,6,4,5,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,10,11,9,8,2,3,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node394Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node394Generator0 else (if j.val < 2 then node394Generator1 else node394Generator2))

def node395Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,14,15,10,11,12,13,7,6,9,8,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,15,14,11,10,13,12,6,7,8,9,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node395Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,5,4,3,2,0,1,14,15,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,7,6,14,15,0,1,2,3,4,5,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node395Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,9,8,11,10,3,2,0,1,15,14,4,5,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,7,6,12,13,0,1,3,2,5,4,14,15,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node395Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node395Generator0 else (if j.val < 2 then node395Generator1 else node395Generator2))

def node396Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,14,15,8,9,10,11,12,13,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,14,15,8,9,10,11,12,13,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node396Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,15,14,8,9,11,10,12,13,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,1,0,2,3,13,12,6,7,9,8,10,11,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node396Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,0,1,7,6,12,13,11,10,8,9,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,0,1,7,6,12,13,11,10,8,9,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node396Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node396Generator0 else (if j.val < 2 then node396Generator1 else node396Generator2))

def node397Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,5,4,7,6,1,0,9,8,15,14,13,12,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,0,1,3,2,5,4,9,8,14,15,13,12,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node397Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,14,15,7,6,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,11,10,9,8,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node397Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node397Generator0 else node397Generator1)

def node398Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,15,14,1,0,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,10,11,5,4,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node398Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,14,15,3,2,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,12,13,0,1,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node398Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node398Generator0 else node398Generator1)

def node399Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,7,6,12,13,15,14,5,4,3,2,1,0,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,3,2,0,1,15,14,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node399Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,5,4,3,2,7,6,9,8,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,5,4,3,2,7,6,9,8,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node399Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,1,0,12,13,7,6,8,9,11,10,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,2,3,0,1,9,8,10,11,13,12,6,7,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node399Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node399Generator0 else (if j.val < 2 then node399Generator1 else node399Generator2))

def node400Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node400Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node400Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node400Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node400Generator0 else (if j.val < 2 then node400Generator1 else node400Generator2))

def node401Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,14,15,9,8,11,10,13,12,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,14,15,9,8,11,10,13,12,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node401Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,15,14,9,8,10,11,12,13,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,0,1,2,3,13,12,7,6,8,9,10,11,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node401Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,0,1,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,0,1,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node401Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node401Generator0 else (if j.val < 2 then node401Generator1 else node401Generator2))

def node402Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,15,14,12,13,1,0,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,15,14,12,13,1,0,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node402Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node402Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node402Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node402Generator0 else (if j.val < 2 then node402Generator1 else node402Generator2))

def node403Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,2,3,1,0,13,12,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,1,0,3,2,14,15,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node403Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,14,15,12,13,3,2,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,12,13,15,14,1,0,2,3,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node403Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node403Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node403Generator0 else (if j.val < 2 then node403Generator1 else node403Generator2))

def node404Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,11,10,7,6,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,9,8,1,0,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node404Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node404Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node404Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node404Generator0 else (if j.val < 2 then node404Generator1 else node404Generator2))

def node405Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,7,6,8,9,3,2,4,5,15,14,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,5,4,6,7,1,0,2,3,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node405Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,3,2,0,1,6,7,5,4,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,7,6,13,12,10,11,0,1,15,14,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node405Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node405Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node405Generator0 else (if j.val < 2 then node405Generator1 else node405Generator2))

def node406Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,14,15,3,2,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,13,12,1,0,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node406Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node406Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node406Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node406Generator0 else (if j.val < 2 then node406Generator1 else node406Generator2))

def node407Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node407Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node407Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,13,12,0,1,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,10,11,2,3,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node407Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node407Generator0 else (if j.val < 2 then node407Generator1 else node407Generator2))

def node408Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,13,12,6,7,1,0,11,10,5,4,14,15,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,1,0,11,10,4,5,15,14,9,8,3,2,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node408Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,7,6,4,5,3,2,0,1,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,6,7,5,4,2,3,1,0,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node408Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,9,8,7,6,12,13,11,10,1,0,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,3,2,0,1,7,6,5,4,11,10,8,9,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node408Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node408Generator0 else (if j.val < 2 then node408Generator1 else node408Generator2))

def node409Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,13,12,15,14,8,9,10,11,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,13,12,15,14,8,9,10,11,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node409Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,3,2,0,1,6,7,4,5,11,10,9,8,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,8,9,6,7,13,12,11,10,1,0,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node409Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,10,11,9,8,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,10,11,9,8,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node409Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node409Generator0 else (if j.val < 2 then node409Generator1 else node409Generator2))

def node410Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node410Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node410Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,13,12,10,11,2,3,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,13,12,1,0,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node410Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node410Generator0 else (if j.val < 2 then node410Generator1 else node410Generator2))

def node411Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,0,1,3,2,13,12,15,14,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,2,3,0,1,15,14,12,13,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node411Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,11,10,9,8,4,5,7,6,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,8,9,11,10,7,6,5,4,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node411Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,15,14,12,13,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,14,15,13,12,1,0,2,3,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node411Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node411Generator0 else (if j.val < 2 then node411Generator1 else node411Generator2))

def node412Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node412Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,12,13,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,15,14,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node412Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,13,12,15,14,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,12,13,14,15,2,3,0,1,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node412Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node412Generator0 else (if j.val < 2 then node412Generator1 else node412Generator2))

def node413Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,11,10,9,8,5,4,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,9,8,11,10,7,6,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node413Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,12,13,5,4,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,14,15,3,2,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node413Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node413Generator0 else node413Generator1)

end SymmetricSubgroupAsymptotics.BinaryActionData16
