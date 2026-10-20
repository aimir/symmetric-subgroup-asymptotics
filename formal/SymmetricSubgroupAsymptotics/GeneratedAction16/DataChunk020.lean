import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
640 through 671. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node704Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,10,11,9,8,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,7,6,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node704Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,0,1,7,6,10,11,12,13,14,15,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,0,1,7,6,15,14,8,9,10,11,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node704Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node704Generator0 else node704Generator1)

def node705Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,3,2,1,0,14,15,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,1,0,3,2,12,13,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node705Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,5,4,6,7,9,8,10,11,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,5,4,6,7,9,8,10,11,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node705Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node705Generator0 else node705Generator1)

def node706Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,0,1,7,6,13,12,11,10,9,8,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,0,1,7,6,13,12,11,10,9,8,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node706Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,15,14,13,12,7,6,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,10,11,9,8,3,2,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node706Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,15,14,2,3,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,15,14,12,13,5,4,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node706Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node706Generator0 else (if j.val < 2 then node706Generator1 else node706Generator2))

def node707Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,12,13,6,7,8,9,10,11,4,5,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,12,13,6,7,8,9,10,11,4,5,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node707Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,0,1,6,7,12,13,11,10,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,0,1,6,7,12,13,11,10,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node707Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,10,11,8,9,7,6,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,11,10,9,8,6,7,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node707Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node707Generator0 else (if j.val < 2 then node707Generator1 else node707Generator2))

def node778Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node778Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node778Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node778Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node778Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,15,14,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node778Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node778Generator0 else node778Generator1) else (if j.val < 3 then node778Generator2 else (if j.val < 4 then node778Generator3 else node778Generator4)))

def node779Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node779Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node779Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node779Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node779Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,2,3,0,1,15,14,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,1,0,3,2,12,13,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node779Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node779Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node779Generator0 else (if j.val < 2 then node779Generator1 else node779Generator2)) else (if j.val < 4 then node779Generator3 else (if j.val < 5 then node779Generator4 else node779Generator5)))

def node780Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node780Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,7,6,5,4,9,8,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,7,6,5,4,9,8,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node780Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node780Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,14,15,12,13,0,1,2,3,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,15,14,13,12,1,0,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node780Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,0,1,2,3,6,7,4,5,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,10,11,8,9,14,15,12,13,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node780Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node780Generator0 else node780Generator1) else (if j.val < 3 then node780Generator2 else (if j.val < 4 then node780Generator3 else node780Generator4)))

def node781Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node781Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,11,10,8,9,6,7,5,4,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,11,10,8,9,6,7,5,4,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node781Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node781Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,2,3,0,1,13,12,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,0,1,2,3,14,15,12,13,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node781Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node781Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node781Generator0 else node781Generator1) else (if j.val < 3 then node781Generator2 else (if j.val < 4 then node781Generator3 else node781Generator4)))

def node782Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node782Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node782Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node782Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,5,4,6,7,8,9,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,5,4,6,7,8,9,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node782Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node782Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node782Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node782Generator0 else (if j.val < 2 then node782Generator1 else node782Generator2)) else (if j.val < 4 then node782Generator3 else (if j.val < 5 then node782Generator4 else node782Generator5)))

def node783Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node783Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,9,8,10,11,4,5,7,6,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,8,9,11,10,5,4,6,7,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node783Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node783Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node783Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node783Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node783Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node783Generator0 else (if j.val < 2 then node783Generator1 else node783Generator2)) else (if j.val < 4 then node783Generator3 else (if j.val < 5 then node783Generator4 else node783Generator5)))

def node784Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node784Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node784Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node784Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,5,4,6,7,8,9,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,5,4,6,7,8,9,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node784Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node784Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node784Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node784Generator0 else (if j.val < 2 then node784Generator1 else node784Generator2)) else (if j.val < 4 then node784Generator3 else (if j.val < 5 then node784Generator4 else node784Generator5)))

def node785Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node785Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node785Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node785Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node785Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,15,14,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node785Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node785Generator0 else node785Generator1) else (if j.val < 3 then node785Generator2 else (if j.val < 4 then node785Generator3 else node785Generator4)))

def node786Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node786Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node786Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node786Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node786Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,15,14,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node786Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node786Generator0 else node786Generator1) else (if j.val < 3 then node786Generator2 else (if j.val < 4 then node786Generator3 else node786Generator4)))

def node787Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node787Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node787Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node787Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,2,3,0,1,12,13,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,1,0,2,3,14,15,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node787Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node787Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node787Generator0 else node787Generator1) else (if j.val < 3 then node787Generator2 else (if j.val < 4 then node787Generator3 else node787Generator4)))

def node788Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node788Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,11,10,9,8,6,7,4,5,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,10,11,8,9,7,6,5,4,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node788Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node788Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,0,1,3,2,14,15,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,3,2,1,0,12,13,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node788Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,15,14,13,12,1,0,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,13,12,14,15,3,2,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node788Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node788Generator0 else node788Generator1) else (if j.val < 3 then node788Generator2 else (if j.val < 4 then node788Generator3 else node788Generator4)))

def node789Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node789Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node789Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node789Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node789Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,15,14,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node789Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node789Generator0 else node789Generator1) else (if j.val < 3 then node789Generator2 else (if j.val < 4 then node789Generator3 else node789Generator4)))

def node790Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node790Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node790Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node790Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node790Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,15,14,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node790Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node790Generator0 else node790Generator1) else (if j.val < 3 then node790Generator2 else (if j.val < 4 then node790Generator3 else node790Generator4)))

def node791Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node791Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node791Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node791Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,15,14,13,12,3,2,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,15,14,13,12,3,2,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node791Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,0,1,2,3,4,5,7,6,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,8,9,11,10,14,15,12,13,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node791Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node791Generator0 else node791Generator1) else (if j.val < 3 then node791Generator2 else (if j.val < 4 then node791Generator3 else node791Generator4)))

def node792Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node792Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node792Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node792Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node792Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,15,14,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node792Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node792Generator0 else node792Generator1) else (if j.val < 3 then node792Generator2 else (if j.val < 4 then node792Generator3 else node792Generator4)))

def node793Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node793Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node793Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node793Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node793Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node793Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node793Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node793Generator0 else (if j.val < 2 then node793Generator1 else node793Generator2)) else (if j.val < 4 then node793Generator3 else (if j.val < 5 then node793Generator4 else node793Generator5)))

def node794Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node794Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node794Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node794Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node794Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node794Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node794Generator0 else node794Generator1) else (if j.val < 3 then node794Generator2 else (if j.val < 4 then node794Generator3 else node794Generator4)))

def node795Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node795Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node795Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node795Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node795Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node795Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node795Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node795Generator0 else (if j.val < 2 then node795Generator1 else node795Generator2)) else (if j.val < 4 then node795Generator3 else (if j.val < 5 then node795Generator4 else node795Generator5)))

def node796Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node796Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node796Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node796Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,0,1,3,2,14,15,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,3,2,1,0,12,13,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node796Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,15,14,13,12,1,0,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,13,12,14,15,3,2,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node796Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node796Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node796Generator0 else (if j.val < 2 then node796Generator1 else node796Generator2)) else (if j.val < 4 then node796Generator3 else (if j.val < 5 then node796Generator4 else node796Generator5)))

def node797Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node797Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node797Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node797Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,13,12,0,1,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,10,11,3,2,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node797Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node797Generator0 else node797Generator1) else (if j.val < 3 then node797Generator2 else node797Generator3))

def node798Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node798Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node798Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node798Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node798Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node798Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node798Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node798Generator0 else (if j.val < 2 then node798Generator1 else node798Generator2)) else (if j.val < 4 then node798Generator3 else (if j.val < 5 then node798Generator4 else node798Generator5)))

def node799Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node799Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,9,8,11,10,4,5,6,7,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,8,9,10,11,5,4,7,6,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node799Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node799Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,3,2,15,14,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,3,2,14,15,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node799Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,12,13,1,0,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,14,15,13,12,0,1,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node799Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node799Generator0 else node799Generator1) else (if j.val < 3 then node799Generator2 else (if j.val < 4 then node799Generator3 else node799Generator4)))

def node800Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node800Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node800Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node800Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node800Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node800Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node800Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node800Generator0 else (if j.val < 2 then node800Generator1 else node800Generator2)) else (if j.val < 4 then node800Generator3 else (if j.val < 5 then node800Generator4 else node800Generator5)))

def node801Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node801Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node801Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node801Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,0,1,10,11,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,0,1,10,11,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node801Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,13,12,2,3,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,13,12,3,2,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node801Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node801Generator0 else node801Generator1) else (if j.val < 3 then node801Generator2 else (if j.val < 4 then node801Generator3 else node801Generator4)))

def node802Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node802Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node802Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node802Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node802Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,14,15,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node802Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,13,12,14,15,2,3,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,12,13,15,14,3,2,1,0,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node802Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node802Generator0 else (if j.val < 2 then node802Generator1 else node802Generator2)) else (if j.val < 4 then node802Generator3 else (if j.val < 5 then node802Generator4 else node802Generator5)))

def node803Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node803Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,4,5,11,10,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,5,4,10,11,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node803Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node803Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node803Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,3,2,0,1,14,15,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,1,0,3,2,12,13,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node803Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node803Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node803Generator0 else (if j.val < 2 then node803Generator1 else node803Generator2)) else (if j.val < 4 then node803Generator3 else (if j.val < 5 then node803Generator4 else node803Generator5)))

def node804Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node804Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node804Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node804Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node804Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,2,3,0,1,13,12,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,0,1,2,3,14,15,12,13,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node804Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node804Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node804Generator0 else (if j.val < 2 then node804Generator1 else node804Generator2)) else (if j.val < 4 then node804Generator3 else (if j.val < 5 then node804Generator4 else node804Generator5)))

def node805Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node805Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node805Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,4,5,6,7,11,10,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,4,5,6,7,10,11,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node805Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node805Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node805Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,12,13,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,12,13,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node805Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node805Generator0 else (if j.val < 2 then node805Generator1 else node805Generator2)) else (if j.val < 4 then node805Generator3 else (if j.val < 5 then node805Generator4 else node805Generator5)))

end SymmetricSubgroupAsymptotics.BinaryActionData16
