import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
320 through 351. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node350Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,10,11,9,8,14,15,12,13,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,3,2,0,1,7,6,4,5,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node350Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,1,0,11,10,4,5,6,7,8,9,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,15,14,8,9,10,11,12,13,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node350Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,14,15,8,9,11,10,13,12,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,14,15,8,9,11,10,13,12,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node350Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node350Generator0 else (if j.val < 2 then node350Generator1 else node350Generator2))

def node351Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node351Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,0,1,6,7,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,0,1,6,7,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node351Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,8,9,0,1,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,14,15,6,7,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node351Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node351Generator0 else (if j.val < 2 then node351Generator1 else node351Generator2))

def node352Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node352Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node352Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,15,14,4,5,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,14,15,5,4,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node352Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node352Generator0 else (if j.val < 2 then node352Generator1 else node352Generator2))

def node353Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,1,0,3,2,15,14,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,3,2,0,1,12,13,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node353Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,8,9,11,10,4,5,7,6,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,8,9,11,10,4,5,7,6,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node353Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,4,5,10,11,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,5,4,11,10,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node353Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node353Generator0 else (if j.val < 2 then node353Generator1 else node353Generator2))

def node354Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,15,14,12,13,0,1,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,15,14,3,2,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node354Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,3,2,1,0,14,15,12,13,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,0,1,2,3,13,12,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node354Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,11,10,9,8,5,4,7,6,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,9,8,11,10,7,6,5,4,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node354Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node354Generator0 else (if j.val < 2 then node354Generator1 else node354Generator2))

def node355Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,0,1,2,3,5,4,15,14,9,8,10,11,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,4,5,7,6,0,1,11,10,12,13,15,14,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node355Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node355Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,8,9,10,11,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,4,5,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node355Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node355Generator0 else (if j.val < 2 then node355Generator1 else node355Generator2))

def node356Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,7,6,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,10,11,9,8,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node356Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,6,7,4,5,2,3,13,12,11,10,9,8,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,6,7,4,5,2,3,13,12,11,10,9,8,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node356Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node356Generator0 else node356Generator1)

def node357Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node357Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,9,8,0,1,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,10,11,7,6,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node357Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,10,11,2,3,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,12,13,1,0,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node357Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node357Generator0 else (if j.val < 2 then node357Generator1 else node357Generator2))

def node358Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,9,8,10,11,4,5,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,10,11,5,4,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node358Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,15,14,12,13,2,3,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,15,14,12,13,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node358Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,10,11,8,9,7,6,5,4,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,11,10,9,8,6,7,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node358Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node358Generator0 else (if j.val < 2 then node358Generator1 else node358Generator2))

def node359Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,5,4,6,7,9,8,10,11,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,5,4,6,7,9,8,10,11,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node359Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node359Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,11,10,8,9,6,7,5,4,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,11,10,8,9,6,7,5,4,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node359Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node359Generator0 else (if j.val < 2 then node359Generator1 else node359Generator2))

def node360Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,5,4,7,6,9,8,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,5,4,7,6,9,8,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node360Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,3,2,1,0,15,14,12,13,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,1,0,2,3,13,12,15,14,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node360Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,15,14,12,13,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,14,15,13,12,1,0,2,3,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node360Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node360Generator0 else (if j.val < 2 then node360Generator1 else node360Generator2))

def node361Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,11,10,4,5,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,15,14,1,0,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node361Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,11,10,8,9,4,5,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,10,11,6,7,5,4,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node361Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node361Generator0 else node361Generator1)

def node362Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,2,3,1,0,7,6,9,8,15,14,12,13,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,2,3,1,0,7,6,9,8,15,14,12,13,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node362Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,11,10,6,7,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,8,9,1,0,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node362Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node362Generator0 else node362Generator1)

def node363Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,9,8,10,11,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,11,10,5,4,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node363Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,9,8,6,7,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,10,11,8,9,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node363Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node363Generator0 else node363Generator1)

def node364Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,15,14,9,8,11,10,13,12,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,15,14,9,8,11,10,13,12,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node364Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,1,0,7,6,12,13,3,2,9,8,14,15,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,9,8,15,14,5,4,11,10,1,0,6,7,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node364Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,14,15,1,0,2,3,12,13,6,7,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,10,11,12,13,14,15,8,9,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node364Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node364Generator0 else (if j.val < 2 then node364Generator1 else node364Generator2))

def node365Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,4,5,3,2,11,10,13,12,6,7,8,9,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,5,4,2,3,10,11,12,13,7,6,9,8,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node365Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,9,8,11,10,15,14,4,5,3,2,0,1,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,0,1,3,2,5,4,14,15,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node365Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,14,15,0,1,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,14,15,0,1,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node365Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node365Generator0 else (if j.val < 2 then node365Generator1 else node365Generator2))

def node366Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node366Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,15,14,3,2,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,13,12,5,4,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node366Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node366Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node366Generator0 else (if j.val < 2 then node366Generator1 else node366Generator2))

def node367Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,15,14,2,3,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,13,12,5,4,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node367Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,15,14,6,7,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,8,9,4,5,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node367Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,11,10,1,0,6,7,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,10,11,0,1,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node367Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node367Generator0 else (if j.val < 2 then node367Generator1 else node367Generator2))

def node368Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,9,8,10,11,5,4,6,7,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,9,8,10,11,5,4,6,7,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node368Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,10,11,8,9,6,7,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,10,11,8,9,6,7,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node368Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,15,14,12,13,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,14,15,13,12,1,0,2,3,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node368Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node368Generator0 else (if j.val < 2 then node368Generator1 else node368Generator2))

def node369Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,9,8,10,11,7,6,5,4,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,11,10,9,8,5,4,6,7,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node369Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node369Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,14,15,3,2,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,13,12,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node369Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node369Generator0 else (if j.val < 2 then node369Generator1 else node369Generator2))

def node370Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,13,12,6,7,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,8,9,3,2,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node370Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node370Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,15,14,5,4,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,15,14,5,4,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node370Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node370Generator0 else (if j.val < 2 then node370Generator1 else node370Generator2))

def node371Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node371Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,11,10,8,9,14,15,13,12,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,1,0,2,3,6,7,5,4,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node371Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node371Generator0 else node371Generator1)

def node372Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,4,5,11,10,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,5,4,10,11,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node372Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,9,8,10,11,4,5,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,10,11,5,4,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node372Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,15,14,12,13,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,15,14,13,12,2,3,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node372Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node372Generator0 else (if j.val < 2 then node372Generator1 else node372Generator2))

def node373Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,12,13,10,11,1,0,14,15,5,4,3,2,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,13,12,11,10,0,1,15,14,4,5,2,3,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node373Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,13,12,2,3,0,1,14,15,4,5,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,10,11,0,1,14,15,13,12,3,2,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node373Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,9,8,14,15,12,13,10,11,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,0,1,15,14,13,12,3,2,8,9,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node373Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node373Generator0 else (if j.val < 2 then node373Generator1 else node373Generator2))

def node374Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,3,2,0,1,4,5,6,7,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,8,9,10,11,13,12,15,14,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node374Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,12,13,14,15,0,1,2,3,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,14,15,13,12,2,3,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node374Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,0,1,3,2,14,15,12,13,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,3,2,1,0,13,12,14,15,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node374Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node374Generator0 else (if j.val < 2 then node374Generator1 else node374Generator2))

def node375Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,5,4,7,6,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,9,8,11,10,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node375Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node375Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node375Generator0 else node375Generator1)

def node376Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,14,15,8,9,11,10,12,13,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,14,15,8,9,11,10,12,13,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node376Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,5,4,15,14,8,9,10,11,13,12,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,0,1,3,2,13,12,6,7,8,9,11,10,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node376Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,0,1,7,6,12,13,11,10,8,9,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,0,1,7,6,12,13,11,10,8,9,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node376Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node376Generator0 else (if j.val < 2 then node376Generator1 else node376Generator2))

def node377Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,11,10,8,9,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,9,8,6,7,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node377Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node377Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node377Generator0 else node377Generator1)

def node378Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,12,13,4,5,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,14,15,2,3,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node378Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,15,14,12,13,0,1,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,14,15,3,2,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node378Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node378Generator0 else node378Generator1)

def node379Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,3,2,1,0,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,3,2,1,0,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node379Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,0,1,7,6,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,0,1,7,6,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node379Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,14,15,7,6,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,9,8,0,1,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node379Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node379Generator0 else (if j.val < 2 then node379Generator1 else node379Generator2))

def node380Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,9,8,2,3,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,12,13,7,6,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node380Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,14,15,6,7,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,8,9,4,5,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node380Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,13,12,5,4,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,15,14,3,2,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node380Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node380Generator0 else (if j.val < 2 then node380Generator1 else node380Generator2))

def node381Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node381Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node381Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,11,10,6,7,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,8,9,1,0,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node381Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node381Generator0 else (if j.val < 2 then node381Generator1 else node381Generator2))

end SymmetricSubgroupAsymptotics.BinaryActionData16
