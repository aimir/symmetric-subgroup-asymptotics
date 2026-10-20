import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
448 through 479. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node512Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node512Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node512Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node512Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,14,15,12,13,1,0,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,14,15,12,13,1,0,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node512Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,4,5,7,6,3,2,0,1,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,4,5,7,6,3,2,0,1,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node512Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node512Generator0 else node512Generator1) else (if j.val < 3 then node512Generator2 else (if j.val < 4 then node512Generator3 else node512Generator4)))

def node513Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node513Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node513Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,4,5,6,7,11,10,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,4,5,6,7,10,11,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node513Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node513Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,12,13,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,15,14,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node513Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node513Generator0 else node513Generator1) else (if j.val < 3 then node513Generator2 else (if j.val < 4 then node513Generator3 else node513Generator4)))

def node514Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node514Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node514Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,4,5,7,6,9,8,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,4,5,7,6,9,8,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node514Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,13,12,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,15,14,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node514Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,8,9,10,11,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,10,11,9,8,4,5,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node514Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node514Generator0 else node514Generator1) else (if j.val < 3 then node514Generator2 else (if j.val < 4 then node514Generator3 else node514Generator4)))

def node515Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node515Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,8,9,11,10,4,5,7,6,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,8,9,11,10,4,5,7,6,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node515Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,0,1,3,2,15,14,12,13,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,2,3,0,1,13,12,15,14,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node515Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,12,13,15,14,3,2,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,13,12,14,15,2,3,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node515Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node515Generator0 else node515Generator1) else (if j.val < 3 then node515Generator2 else node515Generator3))

def node516Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,5,4,6,7,9,8,10,11,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,5,4,6,7,9,8,10,11,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node516Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,11,10,8,9,7,6,4,5,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,10,11,9,8,6,7,5,4,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node516Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,0,1,2,3,15,14,13,12,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,13,12,15,14,2,3,0,1,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node516Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node516Generator0 else (if j.val < 2 then node516Generator1 else node516Generator2))

def node517Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node517Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,9,8,10,11,5,4,6,7,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,9,8,10,11,5,4,6,7,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node517Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,9,8,10,11,5,4,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,9,8,10,11,5,4,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node517Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node517Generator0 else (if j.val < 2 then node517Generator1 else node517Generator2))

def node518Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,0,1,2,3,5,4,6,7,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,9,8,10,11,14,15,13,12,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node518Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,1,0,2,3,7,6,4,5,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,10,11,9,8,13,12,14,15,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node518Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,14,15,2,3,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,15,14,12,13,0,1,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node518Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node518Generator0 else (if j.val < 2 then node518Generator1 else node518Generator2))

def node519Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node519Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,0,1,3,2,14,15,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,3,2,0,1,12,13,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node519Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,5,4,6,7,8,9,11,10,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,5,4,6,7,8,9,11,10,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node519Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,10,11,9,8,6,7,5,4,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,11,10,8,9,7,6,4,5,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node519Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node519Generator0 else node519Generator1) else (if j.val < 3 then node519Generator2 else node519Generator3))

def node520Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,12,13,0,1,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,14,15,12,13,0,1,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node520Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,1,0,3,2,4,5,7,6,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,8,9,11,10,15,14,12,13,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node520Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,8,9,10,11,15,14,13,12,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,2,3,0,1,4,5,6,7,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node520Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node520Generator0 else (if j.val < 2 then node520Generator1 else node520Generator2))

def node521Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,8,9,11,10,13,12,15,14,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,0,1,2,3,4,5,7,6,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node521Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,0,1,2,3,4,5,7,6,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,8,9,11,10,15,14,12,13,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node521Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node521Generator0 else node521Generator1)

def node522Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node522Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node522Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,5,4,6,7,8,9,11,10,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,5,4,6,7,8,9,11,10,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node522Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,11,10,9,8,7,6,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,11,10,9,8,7,6,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node522Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node522Generator0 else node522Generator1) else (if j.val < 3 then node522Generator2 else node522Generator3))

def node523Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node523Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,1,0,3,2,14,15,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,3,2,1,0,12,13,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node523Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,15,14,13,12,2,3,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,12,13,14,15,0,1,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node523Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,13,12,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,12,13,14,15,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node523Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,11,10,9,8,5,4,7,6,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,9,8,11,10,7,6,5,4,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node523Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node523Generator0 else node523Generator1) else (if j.val < 3 then node523Generator2 else (if j.val < 4 then node523Generator3 else node523Generator4)))

def node524Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,9,8,10,11,14,15,13,12,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,3,2,1,0,5,4,6,7,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node524Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,13,12,14,15,0,1,2,3,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,15,14,12,13,3,2,1,0,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node524Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node524Generator0 else node524Generator1)

def node525Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,10,11,8,9,12,13,14,15,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,2,3,1,0,6,7,4,5,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node525Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,15,14,12,13,2,3,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,13,12,14,15,0,1,2,3,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node525Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node525Generator0 else node525Generator1)

def node526Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node526Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,10,11,9,8,3,2,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,12,13,15,14,7,6,4,5,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node526Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,10,11,9,8,2,3,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,12,13,15,14,7,6,4,5,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node526Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node526Generator0 else (if j.val < 2 then node526Generator1 else node526Generator2))

def node527Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node527Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,11,10,9,8,7,6,5,4,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,11,10,9,8,7,6,5,4,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node527Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,1,0,2,3,15,14,12,13,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,2,3,0,1,13,12,15,14,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node527Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,15,14,13,12,1,0,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,14,15,12,13,0,1,2,3,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node527Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node527Generator0 else node527Generator1) else (if j.val < 3 then node527Generator2 else node527Generator3))

def node528Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node528Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,0,1,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,0,1,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node528Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node528Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,10,11,1,0,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,11,10,0,1,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node528Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node528Generator0 else node528Generator1) else (if j.val < 3 then node528Generator2 else node528Generator3))

def node529Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node529Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,9,8,11,10,5,4,7,6,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,9,8,11,10,5,4,7,6,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node529Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,3,2,0,1,13,12,14,15,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,0,1,2,3,14,15,12,13,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node529Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,13,12,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,14,15,13,12,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node529Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node529Generator0 else node529Generator1) else (if j.val < 3 then node529Generator2 else node529Generator3))

def node530Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,3,2,1,0,12,13,14,15,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,12,13,15,14,3,2,0,1,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node530Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,15,14,12,13,1,0,2,3,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,14,15,13,12,1,0,2,3,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node530Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,4,5,7,6,9,8,10,11,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,4,5,7,6,9,8,10,11,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node530Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node530Generator0 else (if j.val < 2 then node530Generator1 else node530Generator2))

def node531Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node531Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,2,3,1,0,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,2,3,1,0,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node531Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node531Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,10,11,1,0,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,11,10,0,1,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node531Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node531Generator0 else node531Generator1) else (if j.val < 3 then node531Generator2 else node531Generator3))

def node532Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,8,9,6,7,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,8,9,6,7,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node532Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,13,12,0,1,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,10,11,3,2,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node532Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,15,14,13,12,2,3,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,14,15,12,13,3,2,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node532Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node532Generator0 else (if j.val < 2 then node532Generator1 else node532Generator2))

def node533Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,9,8,10,11,14,15,12,13,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,0,1,3,2,5,4,6,7,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node533Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,14,15,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,15,14,1,0,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node533Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,15,14,12,13,1,0,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,15,14,12,13,1,0,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node533Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node533Generator0 else (if j.val < 2 then node533Generator1 else node533Generator2))

def node534Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,10,11,9,8,14,15,13,12,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,1,0,3,2,7,6,4,5,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node534Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,3,2,1,0,5,4,6,7,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,9,8,10,11,14,15,12,13,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node534Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node534Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node534Generator0 else (if j.val < 2 then node534Generator1 else node534Generator2))

def node535Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node535Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,15,14,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,15,14,13,12,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node535Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,14,15,0,1,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,13,12,14,15,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node535Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node535Generator0 else (if j.val < 2 then node535Generator1 else node535Generator2))

def node536Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node536Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,11,10,8,9,7,6,4,5,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,10,11,9,8,6,7,5,4,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node536Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node536Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node536Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node536Generator0 else node536Generator1) else (if j.val < 3 then node536Generator2 else node536Generator3))

def node537Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node537Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,11,10,8,9,7,6,4,5,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,10,11,9,8,6,7,5,4,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node537Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node537Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node537Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node537Generator0 else node537Generator1) else (if j.val < 3 then node537Generator2 else node537Generator3))

def node538Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node538Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,11,10,8,9,7,6,4,5,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,10,11,9,8,6,7,5,4,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node538Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node538Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node538Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node538Generator0 else node538Generator1) else (if j.val < 3 then node538Generator2 else node538Generator3))

def node539Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,10,11,8,9,6,7,4,5,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,10,11,8,9,6,7,4,5,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node539Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,13,12,1,0,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,13,12,14,15,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node539Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,15,14,13,12,0,1,2,3,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,0,1,3,2,15,14,12,13,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node539Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node539Generator0 else (if j.val < 2 then node539Generator1 else node539Generator2))

def node540Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node540Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,2,3,1,0,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,2,3,1,0,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node540Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node540Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,15,14,4,5,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,14,15,5,4,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node540Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node540Generator0 else node540Generator1) else (if j.val < 3 then node540Generator2 else node540Generator3))

def node541Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node541Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,9,8,11,10,5,4,7,6,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,9,8,11,10,5,4,7,6,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node541Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,2,3,1,0,13,12,14,15,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,0,1,2,3,14,15,12,13,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node541Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,13,12,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,14,15,13,12,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node541Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node541Generator0 else node541Generator1) else (if j.val < 3 then node541Generator2 else node541Generator3))

def node542Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,5,4,11,10,8,9,6,7,13,12,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,3,2,8,9,6,7,5,4,11,10,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node542Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,11,10,9,8,7,6,13,12,3,2,1,0,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,1,0,7,6,5,4,3,2,9,8,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node542Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,13,12,2,3,8,9,15,14,5,4,10,11,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,4,5,11,10,1,0,6,7,12,13,3,2,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node542Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node542Generator0 else (if j.val < 2 then node542Generator1 else node542Generator2))

def node543Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,9,8,11,10,4,5,6,7,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,8,9,10,11,5,4,7,6,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node543Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,13,12,15,14,3,2,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,12,13,14,15,2,3,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node543Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,5,4,6,7,10,11,9,8,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,5,4,6,7,11,10,8,9,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node543Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node543Generator0 else (if j.val < 2 then node543Generator1 else node543Generator2))

end SymmetricSubgroupAsymptotics.BinaryActionData16
