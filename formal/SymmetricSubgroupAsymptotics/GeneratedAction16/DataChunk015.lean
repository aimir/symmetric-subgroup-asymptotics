import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
480 through 511. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node544Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,12,13,14,15,3,2,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,12,13,14,15,2,3,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node544Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,14,15,13,12,3,2,1,0,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,1,0,3,2,12,13,15,14,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node544Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node544Generator0 else node544Generator1)

def node545Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,12,13,15,14,3,2,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,13,12,14,15,3,2,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node545Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node545Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,10,11,8,9,4,5,6,7,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,8,9,10,11,6,7,4,5,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node545Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node545Generator0 else (if j.val < 2 then node545Generator1 else node545Generator2))

def node546Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node546Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node546Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node546Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node546Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node546Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node546Generator0 else node546Generator1) else (if j.val < 3 then node546Generator2 else (if j.val < 4 then node546Generator3 else node546Generator4)))

def node547Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,2,3,1,0,6,7,5,4,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,6,7,13,12,10,11,1,0,14,15,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node547Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,12,13,14,15,9,8,11,10,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,1,0,10,11,12,13,7,6,9,8,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node547Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,6,7,5,4,2,3,9,8,14,15,13,12,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,6,7,5,4,2,3,9,8,14,15,13,12,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node547Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node547Generator0 else (if j.val < 2 then node547Generator1 else node547Generator2))

def node548Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,2,3,1,0,14,15,12,13,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,12,13,14,15,1,0,2,3,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node548Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,15,14,13,12,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,15,14,3,2,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node548Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node548Generator0 else node548Generator1)

def node549Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node549Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,15,14,12,13,0,1,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,13,12,14,15,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node549Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node549Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node549Generator0 else (if j.val < 2 then node549Generator1 else node549Generator2))

def node550Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node550Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node550Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,12,13,14,15,4,5,7,6,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,8,9,11,10,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node550Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node550Generator0 else (if j.val < 2 then node550Generator1 else node550Generator2))

def node551Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,10,11,9,8,14,15,13,12,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,0,1,2,3,7,6,4,5,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node551Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,1,0,3,2,6,7,5,4,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,11,10,8,9,13,12,15,14,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node551Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,9,8,11,10,14,15,13,12,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,0,1,2,3,5,4,7,6,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node551Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node551Generator0 else (if j.val < 2 then node551Generator1 else node551Generator2))

def node552Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,6,7,5,4,11,10,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,7,6,4,5,10,11,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node552Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,12,13,15,14,2,3,1,0,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,0,1,3,2,15,14,12,13,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node552Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,0,1,2,3,15,14,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,3,2,0,1,12,13,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node552Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node552Generator0 else (if j.val < 2 then node552Generator1 else node552Generator2))

def node553Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,8,9,11,10,5,4,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,9,8,10,11,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node553Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,11,10,8,9,7,6,4,5,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,10,11,9,8,6,7,5,4,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node553Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,2,3,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,14,15,13,12,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node553Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node553Generator0 else (if j.val < 2 then node553Generator1 else node553Generator2))

def node554Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,15,14,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,12,13,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node554Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,1,0,2,3,5,4,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,4,5,7,6,0,1,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node554Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,7,6,0,1,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,1,0,2,3,5,4,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node554Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node554Generator0 else (if j.val < 2 then node554Generator1 else node554Generator2))

def node555Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,12,13,14,15,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,15,14,12,13,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node555Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,8,9,11,10,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,4,5,7,6,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node555Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node555Generator0 else node555Generator1)

def node556Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,0,1,3,2,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,2,3,0,1,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node556Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,13,12,14,15,3,2,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,12,13,15,14,2,3,1,0,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node556Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node556Generator0 else node556Generator1)

def node557Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,8,9,10,11,7,6,5,4,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,11,10,9,8,4,5,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node557Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,14,15,0,1,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,13,12,15,14,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node557Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,9,8,10,11,4,5,6,7,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,8,9,10,11,5,4,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node557Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node557Generator0 else (if j.val < 2 then node557Generator1 else node557Generator2))

def node558Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node558Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,2,3,0,1,13,12,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,0,1,2,3,13,12,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node558Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,8,9,11,10,5,4,7,6,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,9,8,11,10,4,5,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node558Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node558Generator0 else (if j.val < 2 then node558Generator1 else node558Generator2))

def node559Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,12,13,14,15,2,3,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,12,13,15,14,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node559Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,11,10,9,8,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,7,6,5,4,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node559Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node559Generator0 else node559Generator1)

def node560Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,11,10,9,8,7,6,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,11,10,9,8,7,6,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node560Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,15,14,2,3,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,14,15,13,12,0,1,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node560Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,11,10,8,9,6,7,5,4,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,11,10,8,9,6,7,5,4,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node560Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node560Generator0 else (if j.val < 2 then node560Generator1 else node560Generator2))

def node561Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node561Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,8,9,10,11,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,15,14,4,5,6,7,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node561Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node561Generator0 else node561Generator1)

def node562Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node562Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,7,6,9,8,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,7,6,9,8,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node562Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node562Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,13,12,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,15,14,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node562Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,8,9,10,11,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,10,11,9,8,4,5,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node562Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node562Generator0 else node562Generator1) else (if j.val < 3 then node562Generator2 else (if j.val < 4 then node562Generator3 else node562Generator4)))

def node563Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,3,2,0,1,6,7,4,5,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,10,11,8,9,13,12,15,14,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node563Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,8,9,11,10,15,14,12,13,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,3,2,0,1,4,5,7,6,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node563Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node563Generator0 else node563Generator1)

def node564Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,0,1,2,3,7,6,5,4,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,11,10,9,8,13,12,15,14,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node564Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,3,2,0,1,6,7,4,5,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,10,11,8,9,13,12,15,14,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node564Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node564Generator0 else node564Generator1)

def node565Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,3,2,0,1,5,4,7,6,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,9,8,11,10,12,13,15,14,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node565Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,12,13,14,15,0,1,2,3,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,14,15,12,13,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node565Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node565Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node565Generator0 else (if j.val < 2 then node565Generator1 else node565Generator2))

def node566Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node566Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,3,2,0,1,15,14,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,1,0,2,3,13,12,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node566Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,2,3,0,1,12,13,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,1,0,3,2,14,15,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node566Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,13,12,15,14,1,0,2,3,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,14,15,12,13,2,3,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node566Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,13,12,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node566Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node566Generator0 else node566Generator1) else (if j.val < 3 then node566Generator2 else (if j.val < 4 then node566Generator3 else node566Generator4)))

def node567Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,13,12,14,15,1,0,2,3,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,15,14,13,12,2,3,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node567Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,10,11,8,9,6,7,5,4,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,11,10,8,9,6,7,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node567Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,0,1,2,3,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,3,2,0,1,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node567Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node567Generator0 else (if j.val < 2 then node567Generator1 else node567Generator2))

def node568Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node568Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,10,11,9,8,5,4,7,6,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,9,8,11,10,7,6,4,5,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node568Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,13,12,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,14,15,13,12,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node568Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node568Generator0 else (if j.val < 2 then node568Generator1 else node568Generator2))

def node569Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,15,14,12,13,7,6,4,5,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,10,11,9,8,1,0,2,3,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node569Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,9,8,10,11,3,2,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,13,12,14,15,5,4,6,7,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node569Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node569Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node569Generator0 else (if j.val < 2 then node569Generator1 else node569Generator2))

def node570Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node570Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,4,5,9,8,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,5,4,9,8,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node570Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node570Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,3,2,0,1,13,12,14,15,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,0,1,2,3,14,15,12,13,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node570Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,13,12,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,15,14,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node570Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node570Generator0 else node570Generator1) else (if j.val < 3 then node570Generator2 else (if j.val < 4 then node570Generator3 else node570Generator4)))

def node571Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node571Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node571Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,7,6,4,5,9,8,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,6,7,5,4,9,8,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node571Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,15,14,2,3,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,14,15,12,13,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node571Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,9,8,10,11,7,6,5,4,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,11,10,9,8,5,4,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node571Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node571Generator0 else node571Generator1) else (if j.val < 3 then node571Generator2 else (if j.val < 4 then node571Generator3 else node571Generator4)))

def node572Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,6,7,5,4,11,10,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,7,6,4,5,10,11,9,8,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node572Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,8,9,10,11,13,12,14,15,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,0,1,2,3,4,5,6,7,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node572Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node572Generator0 else node572Generator1)

def node573Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node573Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,7,6,5,4,3,2,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,7,6,5,4,3,2,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node573Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node573Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,9,8,6,7,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,8,9,7,6,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node573Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node573Generator0 else node573Generator1) else (if j.val < 3 then node573Generator2 else node573Generator3))

def node574Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,9,8,10,11,4,5,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,8,9,10,11,5,4,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node574Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,14,15,13,12,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,15,14,13,12,2,3,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node574Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,10,11,9,8,5,4,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,9,8,10,11,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node574Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node574Generator0 else (if j.val < 2 then node574Generator1 else node574Generator2))

def node575Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,9,8,10,11,4,5,6,7,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,8,9,10,11,5,4,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node575Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,2,3,12,13,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,2,3,15,14,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node575Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node575Generator0 else node575Generator1)

end SymmetricSubgroupAsymptotics.BinaryActionData16
